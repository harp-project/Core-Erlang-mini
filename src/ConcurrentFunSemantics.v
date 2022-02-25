(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.

Import ListNotations.

Definition Mailbox : Set := list Exp.
Definition ProcessFlag : Set := bool.
Definition LiveProcess : Set := FrameStack * Exp * Mailbox * (list PID) * ProcessFlag.
Definition DeadProcess : Set := list (PID * Exp).
Definition Process : Set := LiveProcess + DeadProcess.

Inductive Signal : Set :=
| Message (e : Exp)
| Exit (r : Exp)
| Link (* TODO *)
| Unlink (* TODO *) .

Inductive Action : Set :=
| ASend (sender receiver : PID) (t : Signal)
| AReceive (t : Exp)
| AArrive (sender receiver : PID) (t : Signal)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Exp)
| AInternal
| ATerminate
| ASetFlag.

Fixpoint find_clause (v : Exp) (c : list (Pat * Exp)) : option (Exp * list Exp) :=
match c with
| [] => None
| (p, e)::xs => match match_pattern p v with
                | None => find_clause v xs
                | Some l => Some (e, l)
                end
end.

Fixpoint receive (m : Mailbox) (c : list (Pat * Exp)) : option (Exp * Exp * list Exp) :=
match m with
| [] => None
| m::ms => match find_clause m c with
           | Some (e, l) => Some (m, e, l)
           | None => receive ms c
           end
end.

Definition pop (v : Exp) (m : Mailbox) := removeFirst Exp_eq_dec v m.

Fixpoint len (l : Exp) : option nat :=
match l with
| ENil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.

Fixpoint mk_list (l : Exp) : option (list Exp) :=
match l with
| ENil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

Definition lit_from_bool (b : bool) : Exp :=
match b with
| true => ELit "true"%string
| false => ELit "false"%string
end.
Definition bool_from_lit (e : Exp) : option bool :=
match e with
| ELit (Atom x) =>
  if eqb x "true"%string
  then Some true
  else if eqb x "false"%string
       then Some false
       else None
| _ => None
end.

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
Inductive processLocalSemantics : Process -> Action -> Process -> Prop :=
(********** LOCAL STEPS **********)
| p_local fs e fs' e' mb links flag :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  inl (fs, e, mb, links, flag) -⌈ AInternal ⌉-> inl (fs', e', mb, links, flag)

(********** SIGNAL ARRIVAL **********)
(* message arrival *)
| p_arrive mb mb' fs e v flag links source dest : VALCLOSED v -> mb' = mb ++ [v] ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Message v) ⌉-> inl (fs, e, mb', links, flag)
(* exiting actions should come here *)
(* dropping exit signals *)
| p_exit_drop fs e mb links flag dest source reason :
  (
    reason = ELit "normal"%string /\ dest <> source /\ flag = false \/
    ~ In source links /\ reason <> ELit "kill"%string
  ) ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason) ⌉->
  inl (fs, e, mb, links, flag)
(* terminating process *)
| p_exit_terminate fs e mb links flag dest source reason reason' :
  (reason = ELit "kill"%string /\ ~ In source links /\ reason' = ELit "killed"%string) \/
  (flag = false /\ reason <> ELit "normal"%string /\ reason' = reason /\ In source links)
 \/
  (reason = ELit "normal"%string /\ source = dest /\ In source links /\ reason' = reason) ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason) ⌉->
  inr (map (fun l => (l, reason')) links)
(* convert exit signal to message *)
(* TODO, NOTE: here tuple should be used instead of list! *)
| p_exit_convert fs e mb links dest source reason :
  (~ In source links /\ reason <> ELit "kill"%string) \/
  In source links ->
  inl (fs, e, mb, links, true) -⌈ AArrive source dest (Exit reason) ⌉->
  inl (fs, e, mb ++ [VCons (ELit "EXIT"%string) 
                           (VCons (EPid source) (VCons reason ENil))], links, true)

(********** SIGNAL SENDING **********)
(* message send *)
| p_send ι v mb fs flag links source : VALCLOSED v ->
  inl (FConcBIF2 (ELit "send"%string) [] [EPid ι] :: fs, v, mb, links, flag)
  -⌈ ASend source ι (Message v) ⌉-> inl (fs, v, mb, links, flag)
(* exit *)
| p_exit fs v mb flag ι self links :
  VALCLOSED v ->
  inl (FConcBIF2 (ELit "exit"%string) [] [EPid ι] :: fs, v, mb, links, flag) -⌈ ASend self ι (Exit v) ⌉->
  inl (fs, ELit "true"%string, mb, links, flag)

(********** SELF **********)
(* self *)
| p_self ι fs mb flag links :
  inl (FConcBIF1 [] :: fs, ELit "self"%string, mb, links, flag) -⌈ ASelf ι ⌉-> inl (fs, EPid ι, mb, links, flag)

(********** SPAWN **********)
(* spawn *)
| p_spawn ι fs mb vl e l flag links :
  Some (length vl) = len l -> VALCLOSED l ->
  inl (FConcBIF2 (ELit "spawn"%string) [] [(EFun vl e)] :: fs, l, mb, links, flag) 
    -⌈ASpawn ι (EFun vl e) l⌉-> inl (fs, EPid ι, mb, links, flag)

(********** RECEVIE **********)
(* receive *)
| p_receive mb l fs e m mb' bindings flag links :
  receive mb l = Some (m, e, bindings) -> mb' = pop m mb
->
  inl (fs, EReceive l, mb, links, flag) -⌈ AReceive m ⌉-> inl (fs, e.[list_subst bindings idsubst], mb', links, flag)

(********** PROCESS FLAG **********)
(* Replace process flags *)
| p_set_flag fs mb flag y v links :
  Some y = bool_from_lit v ->
  inl (FConcBIF2 (ELit "process_flag"%string) [] [ELit "trap_exit"%string] :: fs, v, mb, links, flag) 
   -⌈ ASetFlag ⌉-> inl (fs, lit_from_bool flag, mb, links, y)

(********** NORMAL TERMINATION **********)
(* termination *)
| p_terminate v mb links flag:
  VALCLOSED v ->
  inl ([], v, mb, links, flag) -⌈ATerminate⌉->
   inr (map (fun l => (l, ELit "normal"%string)) links) (* TODO: is internal enough here? *)

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> nat -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x 0 [] x
| lsstep x l ls y z k : r x l y -> LabelStar r y k ls z -> LabelStar r x (S k) (l::ls) z.

Notation "x -⌈ k | xs ⌉-> y" := (LabelStar processLocalSemantics x k xs y) (at level 50).

(******************************************************************************)
(****************************   NODES  ****************************************)
(******************************************************************************)

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Exp_eq_dec; apply Nat.eq_dec. Qed.

Definition Ether : Set := list (PID * PID * Signal).
Definition etherPop := removeFirst (prod_eqdec (prod_eqdec Nat.eq_dec Nat.eq_dec) Signal_eq_dec).

Definition ProcessPool : Set := (PID -> option Process).
Definition Node : Set := Ether * ProcessPool.

Definition nullpool : ProcessPool := fun ι => None.
Definition update (pid : PID) (p : option Process) (n : ProcessPool) :=
  fun ι => if Nat.eq_dec pid ι then p else n ι.

Notation "pid : p |||| n" := (update pid (Some p) n) (at level 32, right associativity).
Notation "n -- pid" := (update pid None n) (at level 31, left associativity).
Lemma update_same : forall ι p p' Π, update ι p (update ι p' Π) = update ι p Π.
Proof.
  intros. unfold update. extensionality ι'.
  break_match_goal; auto.
Qed.
Corollary par_same :  forall ι p p' Π, ι : p |||| ι : p' |||| Π = ι : p |||| Π.
Proof.
  intros. apply update_same.
Qed.

Lemma update_swap : forall ι ι' p p' Π, ι <> ι' ->
   update ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. unfold update. extensionality ι''.
  break_match_goal; auto.
  subst. break_match_goal; auto. congruence.
Qed.
Corollary par_swap :  forall ι ι' p p' Π, ι <> ι' ->
   ι : p |||| ι' : p' |||| Π = ι' : p' |||| ι : p |||| Π.
Proof.
  intros. now apply update_swap.
Qed.
Lemma nullpool_remove : forall ι, nullpool -- ι = nullpool.
Proof.
  intros. extensionality ι'.
  unfold update. break_match_goal; auto.
Qed.

Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
(* sending any signal *)
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι ι' t⌉-> p'
->
  (ether, ι : p |||| prs) -[ASend ι ι' t | ι]ₙ->  (ether ++ [(ι, ι', t)], ι : p' |||| prs)

(** This leads to the loss of determinism: *)
(* arrial of any signal *)
| n_arrive ι ι0 p p' ether prs t:
  In (ι0, ι, t) ether ->
  p -⌈AArrive ι0 ι t⌉-> p' ->
  (ether, ι : p |||| prs) -[AArrive ι0 ι t | ι]ₙ-> (etherPop (ι0, ι, t) ether,
                                            ι : p' |||| prs)
(* internal actions *)
| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = AInternal \/ a = ASelf ι \/ (exists t, a = AReceive t) \/ a = ATerminate \/ a = ASetFlag)
->
   (ether, ι : p |||| Π) -[a| ι]ₙ-> (ether, ι : p' |||| Π)

(* spawning processes *)
| n_spawn Π p p' v1 v2 l ι ι' ether:
  mk_list v2 = Some l -> (ι : p |||| Π) ι' = None ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι : p |||| Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π)

(* Process termination, no more notifyable links *)
| n_terminate ether ι Π :
  (ether, ι : inr [] |||| Π) -[ATerminate | ι]ₙ-> (ether, Π -- ι)

where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

Reserved Notation "n -[ k | l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> nat -> list (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ 0 | [] ]ₙ->* n (* ' *)
| n_trans n n' n'' k l a ι:
  n -[a|ι]ₙ-> n' -> n' -[k|l]ₙ->* n''
->
  n -[S k | (a,ι)::l]ₙ->* n''
where "n -[ k | l ]ₙ->* n'" := (closureNodeSem n k l n').

Theorem closureNodeSem_trans :
  forall n n' k l, n -[k | l]ₙ->* n' -> forall n'' k' l', n' -[k'|l']ₙ->* n''
->
  n -[k + k' | l ++ l']ₙ->* n''.
Proof.
  intros n n' k l D1. induction D1; intros; simpl.
  * exact H.
  * eapply n_trans. exact H.
    eapply IHD1 in H0. exact H0.
Qed.
