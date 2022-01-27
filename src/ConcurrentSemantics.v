(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.

Import ListNotations.

Definition Mailbox : Set := list Exp.
Definition Process : Set := FrameStack * Exp * Mailbox.

Inductive Action : Set :=
| ASend (p : PID) (t : Exp)
| AReceive (t : Exp)
| AArrive (t : Exp)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Exp)
| AInternal.

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

Definition pop (v : Exp) (m : Mailbox) := remove Exp_eq_dec v m.

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

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
Inductive processLocalSemantics : Process -> Action -> Process -> Prop :=
| p_local fs e fs' e' mb :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  (fs, e, mb) -⌈ AInternal ⌉-> (fs', e', mb)

| p_send_local1 fs e ι mb :
  (fs, ESend ι e, mb) -⌈ AInternal ⌉-> (FSend1 e :: fs, ι, mb)
| p_send_local2 fs e v mb : VALCLOSED v ->
  (FSend1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSend2 v :: fs, e, mb)
| p_spawn_local1 fs e ι mb :
  (fs, ESpawn ι e, mb) -⌈ AInternal ⌉-> (FSpawn1 e :: fs, ι, mb)
| p_spawn_local2 fs e v mb : VALCLOSED v ->
  (FSpawn1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSpawn2 v :: fs, e, mb)


| p_arrive mb mb' fs e v : VALCLOSED v -> mb' = mb ++ [v] ->
  (fs, e, mb) -⌈ AArrive v ⌉-> (fs, e, mb')

| p_send ι v mb fs : 
  (FSend2 (EPid ι) :: fs, v, mb) -⌈ ASend ι v ⌉-> (fs, v, mb)

| p_self ι fs mb :
  ( fs, ESelf, mb ) -⌈ ASelf ι ⌉-> ( fs, EPid ι, mb )

| p_spawn ι fs mb vl e l:
  Some (length vl) = len l ->
  (FSpawn2 (EFun vl e) :: fs, l, mb) -⌈ASpawn ι (EFun vl e) l⌉-> (fs, EPid ι, mb)

| p_receive mb l fs e m mb' bindings :
  receive mb l = Some (m, e, bindings) -> mb' = pop m mb
->
  (fs, EReceive l, mb) -⌈ AReceive m ⌉-> (fs, e.[list_subst bindings idsubst], mb')

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> nat -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x 0 [] x
| lsstep x l ls y z k : r x l y -> LabelStar r y k ls z -> LabelStar r x (S k) (l::ls) z.

Notation "x -⌈ k | xs ⌉-> y" := (LabelStar processLocalSemantics x k xs y) (at level 50).

(******************************************************************************)
(****************************   NODES  ****************************************)
(******************************************************************************)

(* Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Module Import NatMap := FMapList.Make(Nat_as_OT). *)
(* From stdpp Require Import natmap fin_maps. *)

Definition Node : Set := list (PID * Process).
Fixpoint put (k : PID) (p : Process) (m : Node) : Node :=
match m with
| [] => [(k, p)]
| (k', p')::xs => if Nat.ltb k k' then (k, p) :: (k', p') :: xs else if Nat.eqb k k' then (k, p)::xs else (k', p') :: (put k p xs)
end.
Fixpoint get (k : PID) (m : Node) : option Process :=
match m with
| [] => None
| (k', p)::xs => if Nat.eqb k k' then Some p else get k xs
end.
Definition dom (m : Node) : list nat := map fst m.

(* Definition Node := natmap Process. Search natmap. *)
Definition nullnode : Node := [].
(* Definition par (pid : PID) (proc: Process) (n : Node) : Node := map_insert pid proc n. *)

Notation "pid : p |||| n" := (put pid p n) (at level 30, right associativity).

(* Definition find (x : PID) (Π : Node) : option Process := lookup x Π. *)

Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
| nsend1 p p' q q' Π Π' (ι ι' : PID) t :
  get ι Π = Some p -> get ι' Π = Some q ->
  Π' = ι : p' |||| ι' : q' |||| Π ->
  p -⌈ASend ι' t⌉-> p' -> q -⌈AArrive t⌉-> q' -> ι <> ι'
->
  Π -[ASend ι' t | ι]ₙ-> Π'

| nsend2 p p' p'' t (ι : PID) Π Π' :
  get ι Π = Some p -> Π' = ι : p'' |||| Π ->
  p -⌈ASend ι t⌉-> p' -> p' -⌈AArrive t⌉-> p'' (** two transitions, because this is atomic! *)
->
  Π -[ASend ι t | ι]ₙ-> Π'

| nsend3 p p' (ι ι' : PID) Π Π' t :
  get ι Π = Some p -> get ι' Π = None ->
  Π' = ι : p' |||| Π ->
  p -⌈ASend ι' t⌉-> p'
->
  Π -[ASend ι' t | ι]ₙ-> Π'

| nreceive p p' t Π Π' (ι : PID) :
  get ι Π = Some p -> Π' = ι : p' |||| Π ->
  p -⌈AReceive t⌉-> p'
->
  Π -[AReceive t | ι]ₙ-> Π'

| ninternal p p' Π Π' (ι : PID) :
  get ι Π = Some p -> Π' = ι : p' |||| Π ->
  p -⌈AInternal⌉-> p'
->
  Π -[AInternal | ι]ₙ-> Π'

| nself p p' Π Π' ι:
  get ι Π = Some p -> Π' = ι : p' |||| Π ->
  p -⌈ASelf ι⌉-> p'
->
  Π -[ASelf ι | ι]ₙ-> Π'

| nspawn Π Π' p p' v1 v2 l ι ι':
  mk_list v2 = Some l -> ~In ι' (dom Π) ->
  get ι Π = Some p -> Π' = ι' : ([], EApp v1 l, []) |||| ι : p' |||| Π ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  Π -[ASpawn ι' v1 v2 | ι]ₙ-> Π'
where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

(*
Fixpoint Pat_eqb (p1 p2 : Pat) : bool :=
match p1, p2 with
 | PLit l, PLit l2 => Z.eqb l l2
 | PPid p, PPid p2 => p =? p2
 | PVar, PVar => true
 | PNil, PNil => true
 | PCons p1 p2, PCons p12 p22 => Pat_eqb p1 p12 && Pat_eqb p2 p22
 | _, _ => false
end.

Fixpoint list_eqb {A} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Fixpoint Exp_eqb (e1 e2 : Exp) : bool :=
match e1, e2 with
 | ELit l, ELit l2 => Z.eqb l l2
 | EPid p, EPid p2 => p =? p2
 | EVar n, EVar n2 => n =? n2
 | EFunId n, EFunId n2 => n =? n2
 | EFun vl e, EFun vl2 e2 => list_eqb String.eqb vl vl2 && Exp_eqb e e2
 | EApp exp l, EApp exp2 l2 => Exp_eqb exp exp2 && list_eqb Exp_eqb l l2
 | ELet v e1 e2, ELet v2 e12 e22 => Exp_eqb e1 e12 && Exp_eqb e12 e22
 | ELetRec f vl b e, ELetRec f2 vl2 b2 e2 => _
 | EPlus e1 e2, EPlus e12 e22 => _
 | ECase e0 p e1 e2, ECase e02 p2 e12 e22 => _
 | ECons e1 e2, ECons e12 e22 => _
 | ENil, ENil => true
 | VCons e1 e2, VCons e12 e22 => _
 | ESend p e, ESend p2 e2 => _
 | EReceive l, EReceive l2 => _
 | _, _ => false
end. *)
(* 
Fixpoint list_eq_Node (l : list (PID * Process)) (n : Node) : Prop :=
match l with
| [] => True
| (p, pr)::xs => find p n = Some pr /\ list_eq_Node xs n
end.

Definition equivalent (n1 n2 : Node) : Prop :=
match n1 with
| {| this := x; sorted := y |} => length n2 = length x /\ list_eq_Node x n2
end. *)

(* #[export] Instance processEq : Equiv Process := eq. *)

Reserved Notation "n -[ k | l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> nat -> list (Action * PID) -> Node -> Prop :=
| nrefl n (* n'  *): (* Permutation n n' -> *) n -[ 0 | [] ]ₙ->* n (* ' *)
| ntrans n n' n'' k l a ι:
  n -[a|ι]ₙ-> n' -> n' -[k|l]ₙ->* n''
->
  n -[S k | (a,ι)::l]ₙ->* n''
where "n -[ k | l ]ₙ->* n'" := (closureNodeSem n k l n').

Ltac perm_solver :=
match goal with
| |- Permutation [] [] => apply perm_nil
| |- Permutation (_::_) (_::_) =>
  tryif apply perm_skip
  then  (idtac "ok")
  else  (idtac "move"; eapply perm_trans; [apply Permutation_cons_append | simpl] )
| _ => idtac "not permutation goal"
end.
Ltac perm_solver_any := repeat perm_solver.
(*
  0 -[ 1 + 1 ]-> 1
  1 -[ 2 ]-> 3
  2 -[ 3 ]-> 3
  3 : 2 + 3 == 5
*)
Goal exists acts k,
  0 : ([], ESend (EPid 1) (EPlus (ELit 1) (ELit 1)), []) ||||
  1 : ([], EReceive [(PVar, ESend (EPid 3) (EVar 0))], []) ||||
  2 : ([], ESend (EPid 3) (ELit 3), []) ||||
  3 : ([], EReceive [(PVar, EReceive [(PVar, EPlus (EVar 0) (EVar 1))])], []) |||| nullnode
  -[ k | acts ]ₙ->*
  0 : ([], ELit 2, []) ||||
  1 : ([], ELit 2, []) ||||
  2 : ([], ELit 3, []) ||||
  3 : ([], ELit 5, []) |||| nullnode.
Proof.
  eexists. exists 18.
  (* Some steps with 0 *)
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_send_local1.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_send_local2. constructor.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  constructor. constructor.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  constructor. constructor. constructor.

  (* Some steps with 2 *)
  eapply ntrans. eapply ninternal with (ι := 2); cbn; try reflexivity.
  apply p_send_local1.
  eapply ntrans. eapply ninternal with (ι := 2); cbn; try reflexivity.
  apply p_send_local2. constructor.
  eapply ntrans. eapply nsend1 with (ι := 2) (ι' := 3); cbn; try reflexivity.
  constructor.
  constructor. constructor. simpl. reflexivity. lia.

  (* Again with 0 *)
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  constructor. constructor.
  eapply ntrans. eapply nsend1 with (ι := 0) (ι' := 1); cbn; try reflexivity.
  constructor. constructor. constructor. reflexivity. lia.
  (* Now with 1 *)
  eapply ntrans. eapply nreceive with (ι := 1); cbn; try reflexivity.
  constructor; try reflexivity.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  apply p_send_local1.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  apply p_send_local2. constructor.
  eapply ntrans. eapply nsend1 with (ι := 1) (ι' := 3); cbn; try reflexivity.
  constructor. constructor. constructor. reflexivity. lia.
  (* Mailbox processing for 3 *)
  eapply ntrans. eapply nreceive with (ι := 3); cbn; try reflexivity.
  constructor; try reflexivity. cbn.
  break_match_goal. 2: congruence.
  break_match_goal. 2: congruence.
  break_match_goal. congruence.
  eapply ntrans. eapply nreceive with (ι := 3); cbn; try reflexivity.
  constructor; try reflexivity.

  eapply ntrans. eapply ninternal with (ι := 3); cbn; try reflexivity.
  constructor. constructor.
  eapply ntrans. eapply ninternal with (ι := 3); cbn; try reflexivity.
  constructor. constructor. constructor.
  eapply ntrans. eapply ninternal with (ι := 3); cbn; try reflexivity.
  constructor. constructor.

  break_match_goal. 2: congruence.
  apply nrefl.
Qed.

(*

let X = spawn(fun() -> receive X -> X ! self() end end, [])
  in let Y = X ! self()
    in receive X -> X end

*)
Goal exists acts k,
  0 : ([], ELet "X"%string (ESpawn (EFun [] (EReceive [(PVar, ESend (EVar 0) ESelf)]
                                            )) ENil)
             (ELet "Y"%string (ESend (EVar 0) ESelf)
                 (EReceive [(PVar, EVar 0)]))
                  , [])
  
  |||| nullnode
  -[ k | acts ]ₙ->*
  0 : ([], EPid 1, []) ||||
  1 : ([], EPid 1, []) |||| nullnode.
Proof.
  eexists. exists 19.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  do 2 constructor.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_spawn_local1.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_spawn_local2. do 2 constructor. intros. inversion H; subst; cbn. 2: inversion H1. repeat constructor.
  eapply ntrans. eapply nspawn with (ι := 0) (ι' := 1); simpl. 2: lia. 2: reflexivity.
  3: constructor. all: simpl; auto.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  do 3 constructor.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  repeat constructor.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  repeat constructor. simpl.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  repeat constructor.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_send_local1.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  apply p_send_local2. constructor.
  eapply ntrans. eapply nself with (ι := 0); cbn; try reflexivity.
  constructor.
  eapply ntrans. eapply nsend1 with (ι := 0) (ι' := 1); cbn; try reflexivity; auto.
  constructor. constructor; auto. constructor.
  eapply ntrans. eapply ninternal with (ι := 0); cbn; try reflexivity.
  repeat constructor. simpl.
  eapply ntrans. eapply nreceive with (ι := 1); cbn; try reflexivity.
  repeat constructor. simpl. break_match_goal. 2: congruence.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  apply p_send_local1.
  eapply ntrans. eapply ninternal with (ι := 1); cbn; try reflexivity.
  apply p_send_local2. constructor.
  eapply ntrans. eapply nself with (ι := 1); cbn; try reflexivity.
  constructor.
  eapply ntrans. eapply nsend1 with (ι := 1) (ι' := 0); cbn; try reflexivity; auto.
  constructor. constructor; auto. constructor. simpl.
  eapply ntrans. eapply nreceive with (ι := 0); simpl; try reflexivity.
  constructor; auto. reflexivity. simpl.
  break_match_goal. 2: congruence.
  apply nrefl.
Qed.

Definition bisimulation (R : Node -> Node -> Prop) :=
  (forall p q p' a ι, R p q -> p -[a | ι]ₙ-> p' -> exists q', q -[a | ι]ₙ-> q' /\ R p' q') /\
  (forall p q q' a ι, R p q -> q -[a | ι]ₙ-> q' -> exists p', p -[a | ι]ₙ-> p' /\ R p' q').

Theorem eq_is_bisim :
  bisimulation eq.
Proof.
  split; intros.
  {
    subst. induction H0.
    * inversion H2. inversion H3. subst. eexists. split. 2: reflexivity.
      eapply nsend1; try eassumption. reflexivity.
    * inversion H1. inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend2; try eassumption. reflexivity.
    * inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend3; try eassumption. reflexivity.
    * inversion H1. subst. eexists. split. 2: reflexivity.
      eapply nreceive; try eassumption. reflexivity.
    * inversion H1; subst.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
  }
  {
    subst. induction H0.
    * inversion H2. inversion H3. subst. eexists. split. 2: reflexivity.
      eapply nsend1; try eassumption. reflexivity.
    * inversion H1. inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend2; try eassumption. reflexivity.
    * inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend3; try eassumption. reflexivity.
    * inversion H1. subst. eexists. split. 2: reflexivity.
      eapply nreceive; try eassumption. reflexivity.
    * inversion H1; subst.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
  }
Qed.

Theorem equivalent_is_bisim :
  bisimulation map_equiv.
Proof.
   split; intros.
  {
    (* subst. induction H0.
    * inversion H2. inversion H3. subst. exists (ι : (fs, t0, mb) |||| ι' : q' |||| q). split.
      eapply nsend1; try eassumption. reflexivity.
    * inversion H1. inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend2; try eassumption. reflexivity.
    * inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend3; try eassumption. reflexivity.
    * inversion H1. subst. eexists. split. 2: reflexivity.
      eapply nreceive; try eassumption. reflexivity.
    * inversion H1; subst.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
  }
  {
    subst. induction H0.
    * inversion H2. inversion H3. subst. eexists. split. 2: reflexivity.
      eapply nsend1; try eassumption. reflexivity.
    * inversion H1. inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend2; try eassumption. reflexivity.
    * inversion H2. subst. eexists. split. 2: reflexivity.
      eapply nsend3; try eassumption. reflexivity.
    * inversion H1. subst. eexists. split. 2: reflexivity.
      eapply nreceive; try eassumption. reflexivity.
    * inversion H1; subst.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity.
      - eexists. split. 2: reflexivity. econstructor; try eassumption. reflexivity. *)
Abort.
