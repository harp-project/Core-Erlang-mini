Require Export SubstSemantics.
Export Relations.Relations.
Export Classes.RelationClasses.

Import ListNotations.

(** Because of this, preorder is enough *)
Goal forall T : Type, forall R : relation T, Reflexive R -> Transitive R ->
  let R' := fun x y => R x y /\ R y x in Reflexive R' /\ Symmetric R' /\ Transitive R'.
Proof.
  intros. split. 2: split.
  * intro. unfold R'. split; apply H.
  * intro. intros. unfold R' in *. destruct H1.
    split; auto.
  * intro. intros. unfold R' in *. destruct H1, H2. split.
    - eapply H0; eauto.
    - eapply H0; eauto.
Qed.

Definition is_value_b (e : Exp) : bool :=
match e with
| ELit _ | EFun _ _ | ERecFun _ _ _ => true
| _ => false
end.

Theorem is_value_equiv :
  forall v, is_value v <-> is_value_b v = true.
Proof.
  split.
  {
    destruct v; intros; inversion H; auto.
  }
  {
    destruct v; intros; simpl in H; try congruence; constructor.
  }
Qed.

Theorem is_value_nequiv :
  forall v, ~ is_value v <-> is_value_b v = false.
Proof.
  split.
  {
    intros; destruct v; auto; exfalso; apply H; constructor.
  }
  {
    intros; destruct v; simpl in H; try congruence; intro; inversion H0.
  }
Qed.

(* I think this definition is not suitable for equivalence:
  - forall v1 v2, which are equivalent:
  e.g. fun() -> 1 ~ fun() -> 1 iff
  forall v1 ~ v2, where `eval fun() -> 1 = v1` (i.e. `v1 = fun() -> 1`) implies `eval fun() -> 1 = v2`
     that means, v2 = fun() -> b, where `eval b = 1`
     This does NOT imply, that `b = 1`, it could be `b = (fun() -> 1)()` too for example

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                   (e1 e2 : Exp)
                 : Prop :=
  (* closed e1 /\ closed e2 /\ *)
  forall m (Hmn : m <= n) v1 v2,
    (Vrel m Hmn v1 v2 /\ (* maybe -> ? *)
     eval m e1 = Res v1) -> (exists clock, eval clock e2 = Res v2)
. *)
Reserved Notation "'EXP' Γ ⊢ e"
         (at level 69, no associativity).

Reserved Notation "'VAL' Γ ⊢ v"
         (at level 69, no associativity).
Inductive ExpScoped (l : list VarFunId) : Exp -> Prop :=
| scoped_var v : In (inl v) l -> EXP l ⊢ EVar v
| scoped_funid f : In (inr f) l -> EXP l ⊢ EFunId f
| scoped_app exp vals : 
  EXP l ⊢ exp -> list_forall (ExpScoped l) vals
->
  EXP l ⊢ EApp exp vals
| scoped_let v e1 e2 :
  EXP l ⊢ e1 -> EXP (l ++ [inl v]) ⊢ e2 
->
  EXP l ⊢ ELet v e1 e2
| scoped_letrec f vl b e :
  EXP (l ++ map inl vl) ⊢ b -> EXP (l ++ [inr f]) ⊢ e
->
  EXP l ⊢ ELetRec f vl b e
| scoped_plus e1 e2 :
  EXP l ⊢ e1 -> EXP l ⊢ e2
->
  EXP l ⊢ EPlus e1 e2
| scoped_if e1 e2 e3 :
  EXP l ⊢ e1 -> EXP l ⊢ e2 -> EXP l ⊢ e3
->
  EXP l ⊢ EIf e1 e2 e3
| scoped_val v :
  VAL l ⊢ v -> EXP l ⊢ v
with ValScoped (l : list VarFunId) : Exp -> Prop :=
| scoped_lit lit : VAL l ⊢ ELit lit
| scoped_fun vl e : EXP (l ++ (map inl vl)) ⊢ e -> VAL l ⊢ EFun vl e
| scoped_recfun f vl e : EXP (l ++ [inr f] ++ (map inl vl)) ⊢ e -> VAL l ⊢ ERecFun f vl e
where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)
and "'VAL' Γ ⊢ e" := (ValScoped Γ e).

Notation "'EXPCLOSED' e" := (EXP [] ⊢ e) (at level 5).
Notation "'VALCLOSED' v" := (VAL [] ⊢ v) (at level 5).

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                   (e1 e2 : Exp)
                 : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall m (Hmn : m <= n) v1,
     eval m e1 = Res v1 -> (exists v2, (exists clock, eval clock e2 = Res v2) /\ Vrel m Hmn v1 v2)
.

Inductive list_biforall {T : Type} (P : T -> T -> Prop) : list T -> list T -> Prop :=
| biforall_nil : list_biforall P [] []
| biforall_cons hd hd' tl tl' : P hd hd' -> list_biforall P tl tl' -> list_biforall P (hd::tl) (hd'::tl').

Check list_eq_dec. Print sumbool.

Definition Vrel_rec (n : nat)
                    (Vrel : forall m, m < n -> Exp -> Exp -> Prop)
                    (v1 v2 : Exp) : Prop :=
  VALCLOSED v1 /\ VALCLOSED v2 /\
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => 
    match list_eq_dec string_dec vl1 vl2 with
    | right _ => False
    | left _ => 
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 -> (* With DB indices, this could be removed *)
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) (varsubst_list vl1 vals1 b1)
                                                                     (varsubst_list vl2 vals2 b2)
    end
  | ERecFun f1 vl1 b1, ERecFun f2 vl2 b2 =>
    match list_eq_dec string_dec vl1 vl2 with
    | right _ => False
    | left _ => 
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 ->
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) (varsubst_list vl1 vals1 (funsubst f1 (ERecFun f1 vl1 b1) b1)) 
                                                                     (varsubst_list vl2 vals2 (funsubst f2 (ERecFun f2 vl2 b2) b2))
    end
  | _, _ => False
  end
.

Definition Vrel : nat -> Exp -> Exp -> Prop :=
  Fix Wf_nat.lt_wf _ Vrel_rec.

Definition Erel (n : nat) (e1 e2 : Exp) : Prop :=
  exp_rel n (fun m _ => Vrel m) e1 e2.

Require Import FunctionalExtensionality Coq.Logic.PropExtensionality.

Lemma Vrel_rec_pointwise {n : nat} :
  forall (f g : forall m : nat, (m < n)%nat -> Exp -> Exp -> Prop),
    (forall (m : nat) (p : (m < n)%nat), f m p = g m p) ->
    Vrel_rec n f = Vrel_rec n g.
Proof.
  intros.
  unfold Vrel_rec.
  extensionality v1.
  extensionality v2.
  destruct v1, v2; auto. break_match_goal. 2: auto.
  f_equal. f_equal.
  extensionality m.
  extensionality Hmn.
  extensionality v1'.
  extensionality v2'.
  rewrite H.
  extensionality l1. extensionality l2.
  extensionality x.
  f_equal.
  extensionality m'.
  extensionality H0.
  trivial.
  
  f_equal. f_equal.
  break_match_goal; auto. extensionality m.
  extensionality Hmn.
  extensionality v1'.
  extensionality v2'.
  rewrite H.
  extensionality l1. extensionality l2.
  extensionality x.
  f_equal.
  extensionality m'.
  extensionality H0.
  trivial.
Qed.

Lemma Vrel_Fix_eq : forall {n : nat} {v1 v2 : Exp},
  Vrel n v1 v2
  = 
  Vrel_rec n (fun (m : nat) (_ : m < n) => Vrel m) v1 v2.
Proof.
  intros.
  unfold Vrel.
  rewrite Fix_eq by (auto using Vrel_rec_pointwise).
  trivial.
Qed.

Section Tests.

  Local Definition e1 := ELit 0.
  Local Definition e2 := EFun [] e1.
  Local Definition e3 := EFun [] (EPlus e1 e1).
  Local Definition inf f := EApp (ERecFun f [] (EApp (EFunId f) [])) [].

  Axiom inf_diverges : forall f clock, eval clock (inf f) = Timeout.

  Goal Erel 0 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e1. split.
    * destruct m; inversion H; inversion Hmn.
    * inversion Hmn. subst. inversion H.
  Qed.
  
  Goal Erel 3 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e1. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H.
      split; try split; try constructor.
  Qed.
  
  Goal Erel 3 e2 e2.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e2. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H. subst. rewrite Vrel_Fix_eq.
      split; try split; repeat constructor.
      simpl.
      intros. apply length_zero_iff_nil in H0. apply length_zero_iff_nil in H1. subst.
      exists e1. split.
      - exists 1. reflexivity.
      - destruct m1; inversion H3. subst.
        split; try split; try constructor.
  Qed.
  
  Goal Erel 3 e2 e3.
  Proof.
    split; try split.
    1-2: repeat constructor.
    exists e3. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H. subst. rewrite Vrel_Fix_eq.
      split; try split; repeat constructor.
      simpl.
      intros. apply length_zero_iff_nil in H0. apply length_zero_iff_nil in H1. subst.
      exists e1. split.
      - exists 3. reflexivity.
      - destruct m1; inversion H3. subst.
        split; try split; repeat constructor.
  Qed.

End Tests.

Scheme le_dep_ind := Induction for le Sort Prop.
Check le_dep_ind. 

Lemma Vrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    Vrel m v1 v2.
Proof.
  induction 1 using le_dep_ind;
    intros;
    eauto.
  rewrite Vrel_Fix_eq.
  rewrite Vrel_Fix_eq in H.
  unfold Vrel_rec at 1.
  unfold Vrel_rec at 1 in H.
  destruct v1, v2; intuition; break_match_hyp; intros.
  epose (H m1 _ vals1 vals2 H0 H1 H2). apply e0. contradiction.
  epose (H m1 _ vals1 vals2 H0 H1 H2). apply e0. contradiction.
  Unshelve. all: lia.
Qed.

Lemma Erel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Exp},
    Erel n e1 e2 ->
    Erel m e1 e2.
Proof.
  intros.
  unfold Erel, exp_rel.
  unfold Erel, exp_rel in H.
  intros. eapply (H m0); eauto. lia.
Qed.
(* 
Lemma exp_rel_trans :
  forall n, Transitive (exp_rel n).

Lemma Vrel_trans :
  forall n, Transitive (Vrel n).
Proof.
  (* induction n.
  *  *)intros. intro. intros. rewrite Vrel_Fix_eq. rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq in H0.
  destruct x, y, z; intuition.
  * simpl in *. lia.
  * simpl in *. repeat break_match_hyp; try contradiction. subst.
    break_match_goal. 2: contradiction.
    intros. (* Here use exp_rel trans! *)
Abort. *)

Theorem fundamental_property :
forall v, (* closed v -> *) is_value v ->
forall n, Vrel n v v.
Proof.
  induction v; intros; try inversion H.
  * constructor.
  * subst.
    rewrite Vrel_Fix_eq. econstructor. instantiate (1 := 1).
  
    unfold Vrel. econstructor.
    destruct H1.
Qed.

