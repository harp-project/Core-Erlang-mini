(**
  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we describe the frame stack semantics for concurrent
  Core Erlang.

  This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576
*)
Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.

Import ListNotations.

Ltac eqb_to_eq_prim :=
  match goal with
  | [H : Nat.eqb _ _ = true  |- _] => apply Nat.eqb_eq  in H
  | [H : Nat.eqb _ _ = false |- _] => apply Nat.eqb_neq in H
  end.

Ltac eqb_to_eq := repeat eqb_to_eq_prim.

Definition Mailbox : Set := list Exp.
Definition ProcessFlag : Set := bool.
Definition LiveProcess : Set := FrameStack * Exp * Mailbox * (list PID) * ProcessFlag.
Definition DeadProcess : Set := list (PID * Exp).
Definition Process : Set := LiveProcess + DeadProcess.

Inductive Signal : Set :=
| Message (e : Exp)
| Exit (r : Exp) (b : bool)
| Link
| Unlink.

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

Notation "'link'" := (ELit "link"%string).
Notation "'spawn'" := (ELit "spawn"%string).
Notation "'unlink'" := (ELit "unlink"%string).
Notation "'exit'" := (ELit "exit"%string).
Notation "'send'" := (ELit "send"%string).
Notation "'normal'" := (ELit "normal"%string).
Notation "'kill'" := (ELit "kill"%string).
Notation "'killed'" := (ELit "killed"%string).
Notation "'EXIT'" := (ELit "EXIT"%string).
Notation "'tt'" := (ELit "true"%string).
Notation "'ff'" := (ELit "false"%string).
Notation "'self'" := (ELit "self"%string).
Notation "'ok'" := (ELit "ok"%string).
Notation "'process_flag'" := (ELit "process_flag"%string).
Notation "'trap_exit'" := (ELit "trap_exit"%string).

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
(*
  Fredlund: https://www.diva-portal.org/smash/get/diva2:8988/FULLTEXT01.pdf
  - it is similar, kill rules on page 66 are quite similar to our exit rules, and both differ from doc.
*)
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
| p_exit_drop fs e mb links flag dest source reason b :
  (
    reason = normal /\ dest <> source /\ flag = false \/
    ~ In source links /\ b = true /\ dest <> source
                                           (*    ^------------ TODO: this check is missing from doc? *)
  ) ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason b) ⌉->
  inl (fs, e, mb, links, flag)
(* terminating process *)
| p_exit_terminate fs e mb links flag dest source reason reason' b :
  (reason = kill /\ b = false /\ reason' = killed) \/
  (flag = false /\ reason <> normal /\ reason' = reason /\ (b = true -> In source links) /\ 
  (b = false -> reason <> kill))
                  (*    ^------------ TODO: this check is missing from doc. *)
 \/
  (flag = false /\ reason = normal /\ source = dest /\ reason' = reason) ->
  (*    ^------------ TODO: this check is missing from doc. *)
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason b) ⌉->
  inr (map (fun l => (l, reason')) links)
(* convert exit signal to message *)
(* TODO, NOTE: here tuple should be used instead of list! *)
| p_exit_convert fs e mb links dest source reason b:
  (b = false /\ reason <> kill) \/
  (b = true /\ In source links)
 ->
  inl (fs, e, mb, links, true) -⌈ AArrive source dest (Exit reason b) ⌉->
  inl (fs, e, mb ++ [VCons EXIT 
                           (VCons (EPid source) (VCons reason ENil))], links, true)
(* link received *)
| p_link_arrived fs e mb links source dest flag:
  inl (fs, e, mb, links, flag) -⌈AArrive source dest Link⌉->
  inl (fs, e, mb, source :: links, flag)

(* unlink received *)
| p_unlink_arrived fs e mb links source dest flag :
  inl (fs, e, mb, links, flag) -⌈AArrive source dest Unlink⌉->
  inl (fs, e, mb, remove Nat.eq_dec source links, flag)

(********** SIGNAL SENDING **********)
(* message send *)
| p_send ι v mb fs flag links source : VALCLOSED v ->
  inl (FBIF2 send [] [EPid ι] :: fs, v, mb, links, flag)
  -⌈ ASend source ι (Message v) ⌉-> inl (fs, v, mb, links, flag)
(* exit, 2 parameters *)
| p_exit fs v mb flag ι selfι links :
  VALCLOSED v ->
  inl (FBIF2 exit [] [EPid ι] :: fs, v, mb, links, flag) -⌈ ASend selfι ι (Exit v false) ⌉->
  inl (fs, tt, mb, links, flag)
(* link *)
| p_link fs ι mb flag links selfι :
  inl (FBIF2 link [] [] :: fs, EPid ι, mb, links, flag) 
  -⌈ASend selfι ι Link⌉->
  inl (fs, ok, mb, ι :: links, flag)
(* unlink *)
| p_unlink fs ι mb flag links selfι :
  inl (FBIF2 unlink [] [] :: fs, EPid ι, mb, links, flag) 
  -⌈ASend selfι ι Unlink⌉->
  inl (fs, ok, mb, remove Nat.eq_dec ι links, flag)
(* DEAD PROCESSES *)
| p_dead ι selfι links reason:
  inr ((ι, reason) :: links) -⌈ASend selfι ι (Exit reason true)⌉-> inr links


(********** SELF **********)
(* self *)
| p_self ι fs mb flag links :
  inl (FBIF1 [] :: fs, self, mb, links, flag) -⌈ ASelf ι ⌉-> inl (fs, EPid ι, mb, links, flag)

(********** SPAWN **********)
(* spawn *)
| p_spawn ι fs mb vl e l flag links :
  Some (length vl) = len l -> VALCLOSED l ->
  inl (FBIF2 spawn [] [(EFun vl e)] :: fs, l, mb, links, flag) 
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
  inl (FBIF2 process_flag [] [trap_exit] :: fs, v, mb, links, flag) 
   -⌈ ASetFlag ⌉-> inl (fs, lit_from_bool flag, mb, links, y)

(********** TERMINATION **********)
(* termination *)
| p_terminate v mb links flag:
  VALCLOSED v ->
  inl ([], v, mb, links, flag) -⌈ATerminate⌉->
   inr (map (fun l => (l, normal)) links) (* NOTE: is internal enough here? - no, it's not for bisimulations *)
(* exit with one parameter *)
| p_exit_self fs v mb links flag :
  VALCLOSED v ->
  inl (FBIF2 exit [] [] :: fs, v, mb, links, flag) -⌈ ATerminate ⌉->
  inr (map (fun e => (e, v)) links)

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x [] x
| lsstep x l ls y z : r x l y -> LabelStar r y ls z -> LabelStar r x (l::ls) z.

Notation "x -⌈ xs ⌉->* y" := (LabelStar processLocalSemantics x xs y) (at level 50).

(******************************************************************************)
(****************************   NODES  ****************************************)
(******************************************************************************)

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Exp_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

Definition update {T : Type} (pid : PID) (p : T) (n : PID -> T) : PID -> T :=
  fun ι => if Nat.eqb pid ι then p else n ι.

(** This representation assures that messages sent from the same process,
    are delivered in the same order *)
Definition Ether : Set := PID -> PID -> list Signal.
Definition etherPop (source dest : PID) (n : Ether) :
  option (Signal * Ether) :=
match n source dest with
| [] => None
| x::xs => Some (x, update source (update dest xs (n source)) n)
end.

Definition ProcessPool : Set := (PID -> option Process).
Definition Node : Set := Ether * ProcessPool.

Definition nullpool : ProcessPool := fun ι => None.

Notation "pid : p |||| n" := (update pid (Some p) n) (at level 32, right associativity).
Notation "n -- pid" := (update pid None n) (at level 31, left associativity).
Lemma update_same : forall T ι (p p' : T) Π, update ι p (update ι p' Π) = update ι p Π.
Proof.
  intros. unfold update. extensionality ι'.
  break_match_goal; auto.
Qed.
Corollary par_same :  forall T ι (p p' : T) Π, ι : p |||| ι : p' |||| Π = ι : p |||| Π.
Proof.
  intros. apply update_same.
Qed.

Lemma update_swap : forall T ι ι' (p p' : T) Π, ι <> ι' ->
   update ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. unfold update. extensionality ι''.
  break_match_goal; auto.
  subst. break_match_goal; auto.
  apply Nat.eqb_eq in Heqb0. apply Nat.eqb_eq in Heqb. congruence.
Qed.
Corollary par_swap :  forall ι ι' (p p' : (option Process)) Π, ι <> ι' ->
   @update (option Process) ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. now apply update_swap.
Qed.
Lemma nullpool_remove : forall ι, nullpool -- ι = nullpool.
Proof.
  intros. extensionality ι'.
  unfold update. break_match_goal; auto.
Qed.

Definition etherAdd (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  update source (update dest (n source dest ++ [m]) (n source) ) n.

Theorem update_noop :
  forall T x (xval : T) n, n x = xval -> update x xval n = n.
Proof.
  intros. extensionality y.
  unfold update. break_match_goal.
  apply Nat.eqb_eq in Heqb. now subst.
  reflexivity.
Qed.

Lemma etherPop_greater :
  forall ι ether s ι' ether', etherPop ι ι' ether = Some (s, ether') ->
  forall ι'' ι''' s', etherPop ι ι' (etherAdd ι'' ι''' s' ether) = Some (s, etherAdd ι'' ι''' s' ether').
Proof.
  intros. unfold etherPop, etherAdd, update in *.
  destruct (Nat.eqb ι'' ι) eqn:Eq1; eqb_to_eq; subst.
  * break_match_hyp; eqb_to_eq; subst; simpl. congruence.
    inversion H.
    break_match_goal.
    - break_match_hyp.
      destruct (ether ι ι'''); simpl in Heql0; inversion Heql0.
      inversion Heql0.
    - break_match_hyp; eqb_to_eq; subst.
      + rewrite Heql in Heql0. simpl in Heql0. inversion Heql0.
        do 3 f_equal.
        extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
        extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
        now do 2 rewrite Nat.eqb_refl.
        rewrite Nat.eqb_refl. apply Nat.eqb_neq in Heqb. now rewrite Heqb.
      + inversion Heql0.
        do 3 f_equal.
        extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
        extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
        do 2 rewrite Nat.eqb_refl. apply Nat.eqb_neq in Heqb. now rewrite Heqb.
        rewrite Nat.eqb_refl. apply not_eq_sym in Heqb.
        apply Nat.eqb_neq in Heqb. rewrite Heqb.
        apply Nat.eqb_neq in Heqb0. now rewrite Heqb0.
  * break_match_hyp; eqb_to_eq; subst; simpl. congruence.
    inversion H.
    break_match_goal.
    - do 3 f_equal.
      extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
      congruence. congruence.
    - do 3 f_equal.
      extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
      extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
      apply not_eq_sym in Heqb.
      apply Nat.eqb_neq in Heqb. rewrite Heqb. now rewrite Nat.eqb_refl.
      apply not_eq_sym in Heqb.
      apply Nat.eqb_neq in Heqb. rewrite Heqb.
      apply Nat.eqb_neq in Heqb0. now rewrite Heqb0.
Qed.

Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
(** sending any signal *)
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι ι' t⌉-> p'
->
  (ether, ι : p |||| prs) -[ASend ι ι' t | ι]ₙ->  (etherAdd ι ι' t ether, ι : p' |||| prs)

(** This leads to the loss of determinism: *)
(** arrial of any signal *)
| n_arrive ι ι0 p p' ether ether' prs t:
  etherPop ι0 ι ether = Some (t, ether') ->
  p -⌈AArrive ι0 ι t⌉-> p' ->
  (ether, ι : p |||| prs) -[AArrive ι0 ι t | ι]ₙ-> (ether',
                                            ι : p' |||| prs)

(* TODO: link sent to non-existing process triggers exit, messages should be discarded when sent to non-existing process *)


(** internal actions *)
| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = AInternal \/ a = ASelf ι \/ (exists t, a = AReceive t) \/ a = ATerminate \/ a = ASetFlag)
->
   (ether, ι : p |||| Π) -[a| ι]ₙ-> (ether, ι : p' |||| Π)

(** spawning processes *)
| n_spawn Π p p' v1 v2 l ι ι' ether:
  mk_list v2 = Some l -> (ι : p |||| Π) ι' = None ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι : p |||| Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π)

(** Process termination, no more notifyable links *)
| n_terminate ether ι Π :
  (ether, ι : inr [] |||| Π) -[ATerminate | ι]ₙ-> (ether, Π -- ι)

where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

(** Refexive, transitive closure, with action logs: *)
Reserved Notation "n -[ l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> list (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ [] ]ₙ->* n (* ' *)
| n_trans n n' n'' l a ι:
  n -[a|ι]ₙ-> n' -> n' -[l]ₙ->* n''
->
  n -[(a,ι)::l]ₙ->* n''
where "n -[ l ]ₙ->* n'" := (closureNodeSem n l n').

Theorem closureNodeSem_trans :
  forall n n' l, n -[l]ₙ->* n' -> forall n'' l', n' -[l']ₙ->* n''
->
  n -[l ++ l']ₙ->* n''.
Proof.
  intros n n' l D1. induction D1; intros; simpl.
  * exact H.
  * eapply n_trans. exact H.
    eapply IHD1 in H0. exact H0.
Qed.
