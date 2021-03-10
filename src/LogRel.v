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
  EXP l ⊢ exp ->
  (forall i, i < length vals -> EXP l ⊢ nth i vals (ELit 0))
->
  EXP l ⊢ EApp exp vals
| scoped_let v e1 e2 :
  EXP l ⊢ e1 -> EXP (l ++ [inl v]) ⊢ e2 
->
  EXP l ⊢ ELet v e1 e2
| scoped_letrec f vl b e :
  EXP (l ++ [inr f] ++ map inl vl) ⊢ b -> EXP (l ++ [inr f]) ⊢ e
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

(** ξ and η assigns closed expressions to vars in Γ 
  Basically this says, ξ and η are equivalent pointwise for Γ
*)

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
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e0. contradiction.
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e0. contradiction.
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
  destruct H, H0. split; auto. split; auto.
  intros. eapply (H1 m0); eauto. lia.
Qed.

Lemma Vrel_closed : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v1 /\ VALCLOSED v2.
Proof.
  intros.
  destruct H as [? [? ?] ].
  destruct v1, v2; intuition.
Qed.

Lemma Vrel_closed_l : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v1.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Hint Resolve Vrel_closed_l.

Lemma Vrel_closed_r : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v2.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Hint Resolve Vrel_closed_r.

Lemma Erel_closed : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros.
  unfold Erel, exp_rel in H.
  intuition.
Qed.

Lemma Erel_closed_l : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Hint Resolve Erel_closed_l.

Lemma Erel_closed_r : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Hint Resolve Erel_closed_r.

(*
Definition subscoped (l l' : list VarFunId) (ξ : VarFunId -> Exp) : Prop :=
  forall v, In v l -> ValScoped l' (ξ v).

Notation "'SUBSCOPE' Γ ⊢ ξ :: Γ'" := (subscoped Γ Γ' ξ) (at level 69, ξ at level 99, no associativity).
*)

Definition subscoped (l' : list VarFunId) (vals : list Exp) : Prop :=
  forall i, i < length vals -> ValScoped l' (nth i vals (ELit 0))
.

(* Def: closed values are related *)
Definition Grel (n : nat) (vals1 vals2 : list Exp) : Prop :=
  subscoped [] vals1 /\ subscoped [] vals2 /\ length vals1 = length vals2 /\
  list_biforall (Vrel n) vals1 vals2.


(** Closing substitutions  *)

(* Definition Grel (n : nat) (Γ : list VarFunId) (ξ η : VarFunId -> Exp) : Prop :=
  (subscoped Γ [] ξ) /\
  (subscoped Γ [] η) /\
  forall x, In x Γ -> Vrel n (ξ x) (η x). *)

Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.
End list_length_ind.

Lemma Grel_downclosed_helper : forall vals1 vals2 m n,
  m <= n -> length vals1 = length vals2 ->
  list_biforall (Vrel n) vals1 vals2 ->
  list_biforall (Vrel m) vals1 vals2.
Proof.
  intro. induction vals1 using list_length_ind; intros.
  destruct vals1, vals2.
  * constructor.
  * inversion H1.
  * inversion H1.
  * inversion H2. subst. constructor. 
    - eapply Vrel_downclosed. eauto.
    - eapply H; eauto.
Unshelve. auto.
Qed.

Lemma Grel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {vals1 vals2 : list Exp},
    Grel n vals1 vals2 ->
    Grel m vals1 vals2.
Proof.
  unfold Grel; intros; intuition. eapply Grel_downclosed_helper; eauto.
Qed.

Corollary app_not_in {T : Type} : forall (x:T) (l1 l2 : list T),
  ~In x l1 -> ~In x l2 -> ~In x (l1 ++ l2).
Proof.
  intros.
  intro. eapply in_app_or in H1. destruct H1; contradiction.
Qed.

Theorem in_list_sound : forall l e, in_list e l = true <-> In e l.
Proof.
  induction l; intros.
  * split; intros; inversion H.
  * split; intros.
    - simpl in H. break_match_hyp.
      + apply eqb_eq in Heqb. simpl. left. auto.
      + apply eqb_neq in Heqb. simpl. right. apply IHl. auto.
    - destruct (eqb e a) eqn:P.
      + apply eqb_eq in P. subst. simpl. rewrite eqb_refl. auto.
      + simpl. rewrite P. apply IHl. inversion H.
        ** apply eqb_neq in P. congruence.
        ** auto.
Qed.

Hint Resolve in_list_sound.

Theorem not_in_list_sound : forall l e, in_list e l = false <-> ~In e l.
Proof.
  induction l; intros.
  * split; intros. intro. inversion H0. reflexivity.
  * split; intros.
    - simpl in H. break_match_hyp.
      + inversion H.
      + apply eqb_neq in Heqb. simpl. intro. inversion H0. symmetry in H1. contradiction.
        eapply IHl; eauto.
    - simpl. break_match_goal.
      apply eqb_eq in Heqb. subst. exfalso. apply H. intuition.
      apply eqb_neq in Heqb. eapply IHl. apply not_in_cons in H. destruct H. auto.
Qed.

Hint Resolve not_in_list_sound.

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Theorem map_not_in {T T' : Type} : forall (l : list T) (x: T) (f : T -> T'),
  Injective f -> ~In x l -> ~In (f x) (map f l).
Proof.
  induction l; intros; intro.
  * inversion H1.
  * inversion H1.
    - apply H in H2. subst. apply H0. intuition.
    - eapply IHl; eauto. apply not_in_cons in H0. destruct H0. auto.
Qed.

Scheme ValScoped_ind2 := Induction for ValScoped Sort Prop
  with ExpScoped_ind2 := Induction for ExpScoped Sort Prop.
Combined Scheme scoped_ind from ValScoped_ind2, ExpScoped_ind2.
Check scoped_ind.

Theorem scoped_ignores_sub_helper vals : forall x l v,
  (forall i : nat,
     i < Datatypes.length vals ->
     forall (x : ExpEnv.Var) (v : Exp),
     ~ In (@inl Var FunctionIdentifier x) l -> varsubst x v (nth i vals (ELit 0)) = nth i vals (ELit 0)) ->
  ~ In (inl x) l ->
  (map (varsubst x v) vals) = vals.
Proof.
  induction vals; intros.
  * reflexivity.
  * simpl. epose (H 0 _ _ _ H0). simpl in e. rewrite e.
    erewrite IHvals; eauto. intros. eapply (H (S i)). simpl. lia. auto.
Unshelve. simpl. lia.
Qed.

Theorem scoped_ignores_sub : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall x v, ~ In (inl x) Γ -> varsubst x v e = e) /\
  (forall e, EXP Γ ⊢ e -> forall x v, ~ In (inl x) Γ -> varsubst x v e = e).
Proof.
  apply scoped_ind.
  * intros. reflexivity.
  * intros. simpl. break_match_goal; auto. rewrite H; auto.
    apply app_not_in; auto. intuition. apply not_in_list_sound in Heqb.
    eapply map_not_in in Heqb. exact (Heqb H1). intro. intros. inversion H2. auto.
  * intros. simpl. break_match_goal; auto. rewrite H; auto.
    repeat apply app_not_in; auto. intro. inversion H1; try congruence. contradiction.
    apply not_in_list_sound in Heqb.
    eapply map_not_in in Heqb. intro. exact (Heqb H1). intro. intros. inversion H1. auto.
  * intros. simpl. break_match_goal; auto. apply eqb_eq in Heqb. subst. contradiction.
  * intros. simpl. auto.
  * intros. simpl. rewrite H; auto. erewrite scoped_ignores_sub_helper; eauto.
  * intros. simpl. break_match_goal.
    - rewrite H; auto.
    - rewrite H, H0; auto. eapply app_not_in; auto.
      intro. inversion H2. 2: contradiction. apply eqb_neq in Heqb. inversion H3. congruence.
  * intros. simpl. break_match_goal; auto.
    - rewrite H0; auto. eapply app_not_in; auto.
      intro. inversion H2; try contradiction; try congruence.
    - rewrite H, H0. auto.
      + eapply app_not_in; auto.
      intro. inversion H2; try contradiction; try congruence.
      + apply app_not_in; auto. Search In map. eapply app_not_in. intro.
        inversion H2; try contradiction; try congruence.
        apply not_in_list_sound in Heqb0.
        eapply map_not_in in Heqb0. intro. exact (Heqb0 H2).
        intro. intros. inversion H2. auto.
  * intros. simpl. rewrite H, H0; auto.
  * intros. simpl. rewrite H, H0, H1; auto.
  * intros. eapply H; eauto.
Qed.

Corollary eclosed_ignores_sub :
  forall e x v,
  EXPCLOSED e -> varsubst x v e = e.
Proof.
  intros. eapply scoped_ignores_sub with (Γ := []). auto. intuition.
Qed.

Corollary vclosed_ignores_sub :
  forall e x v,
  VALCLOSED e -> varsubst x v e = e.
Proof.
  intros. pose (scoped_ignores_sub []). destruct a. apply H0. auto. intuition.
Qed.

Theorem scoped_ignores_funsub_helper vals : forall x l v,
  (forall i : nat,
     i < Datatypes.length vals ->
     forall (x : FunctionIdentifier) (v : Exp),
     ~ In (@inr Var FunctionIdentifier x) l -> funsubst x v (nth i vals (ELit 0)) = nth i vals (ELit 0)) ->
  ~ In (inr x) l ->
  (map (funsubst x v) vals) = vals.
Proof.
  induction vals; intros.
  * reflexivity.
  * simpl. epose (H 0 _ _ _ H0). simpl in e. rewrite e.
    erewrite IHvals; eauto. intros. eapply (H (S i)). simpl. lia. auto.
Unshelve. simpl. lia.
Qed.

Lemma inr_inl_map x l:
  In (@inr Var FunctionIdentifier x) (map inl l) -> False.
Proof.
  induction l; intros; inversion H.
  inversion H0. apply IHl. auto.
Qed.

Theorem scoped_ignores_funsub : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall x v, ~ In (inr x) Γ -> funsubst x v e = e) /\
  (forall e, EXP Γ ⊢ e -> forall x v, ~ In (inr x) Γ -> funsubst x v e = e).
Proof.
  apply scoped_ind.
  * intros. reflexivity.
  * intros. simpl. rewrite H; auto.
    apply app_not_in; auto. intuition.
    apply inr_inl_map in H1. auto.
  * intros. simpl. break_match_goal; auto.
    rewrite H; auto.
    repeat apply app_not_in; auto.
    intro. inversion H1. inversion H2. apply funid_eqb_neq in Heqb. 1-2: contradiction.
    exact (inr_inl_map x vl).
  * intros. simpl. auto.
  * intros. simpl. break_match_goal; auto. apply funid_eqb_eq in Heqb. subst. contradiction.
  * intros. simpl. rewrite H; auto. erewrite scoped_ignores_funsub_helper; eauto.
  * intros. simpl. rewrite H, H0; auto. eapply app_not_in; auto.
      intro. inversion H2. 2: contradiction. inversion H3.
  * intros. simpl. break_match_goal; auto.
    - rewrite H, H0. auto.
      + eapply app_not_in; auto.
        intro. inversion H2. 2: contradiction. inversion H3. subst.
        pose (funid_eqb_refl x). rewrite e5 in Heqb0. inversion Heqb0.
      + apply app_not_in; auto. eapply app_not_in.
        intro. inversion H2; inversion H3. subst. apply funid_eqb_neq in Heqb0. congruence.
        exact (inr_inl_map x vl).
  * intros. simpl. rewrite H, H0; auto.
  * intros. simpl. rewrite H, H0, H1; auto.
  * intros. eapply H; eauto.
Qed.

Corollary eclosed_ignores_funsub :
  forall e x v,
  EXPCLOSED e -> funsubst x v e = e.
Proof.
  intros. eapply scoped_ignores_funsub with (Γ := []). auto. intuition.
Qed.

Corollary vclosed_ignores_funsub :
  forall e x v,
  VALCLOSED e -> funsubst x v e = e.
Proof.
  intros. pose (scoped_ignores_funsub []). destruct a. apply H0. auto. intuition.
Qed.



(** Closing substitution *)
Definition subst (v' : VarFunId) (what wher : Exp) : Exp :=
  match v' with
  | inl v => varsubst v what wher
  | inr f => funsubst f what wher
  end.

Lemma subst_ignores_var : forall v v' val, inl v <> v' -> subst v' val (EVar v) = EVar v.
Proof.
  intros. unfold subst. simpl. destruct v'; auto.
  break_match_goal; auto. apply eqb_eq in Heqb. subst. congruence.
Qed.

Lemma subst_ignores_funid : forall v v' val, inr v <> v' -> subst v' val (EFunId v) = EFunId v.
Proof.
  intros. unfold subst. simpl. destruct v'; auto.
  break_match_goal; auto. apply funid_eqb_eq in Heqb. subst. congruence.
Qed.

Definition subst_list (l : list VarFunId) (es : list Exp) (e : Exp) : Exp :=
  fold_left (fun acc '(v, val) => subst v val acc) (combine l es) e.

Check scoped_ind.
Check Exp_ind2.

Theorem scope_duplicate :
  forall e Γ v, In v Γ -> EXP (v :: Γ) ⊢ e -> EXP Γ ⊢ e.
Proof.
  einduction e using Exp_ind2 with 
      (Q := fun l => list_forall (fun e => forall Γ v, In v Γ -> EXP (v :: Γ) ⊢ e -> EXP Γ ⊢ e) l); intros.
  * constructor. constructor.
  * inversion H0. subst. 2: inversion H1. constructor. inversion H2; subst; auto.
  * inversion H0. subst. 2: inversion H1. constructor. inversion H2; subst; auto.
  * constructor. constructor. inversion H0. inversion H1. subst.
    rewrite <- app_comm_cons in H4. apply IHe0 in H4; auto. apply in_or_app. left. auto.
  * constructor. constructor. inversion H0. inversion H1. subst.
    rewrite <- app_comm_cons in H4. apply IHe0 in H4; auto. apply in_or_app. left. auto.
  * inversion H0. 2: inversion H1. subst. rewrite indexed_to_forall in IHe1.
    constructor.
    - eapply IHe0; eauto.
    - intros. eapply IHe1; eauto.
  * inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. exact H. auto.
    - rewrite <- app_comm_cons in H5. eapply IHe0_2. 2: exact H5.
      apply in_or_app. left. auto.
  * inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. apply in_or_app. left. eauto. rewrite <- app_comm_cons in H3. auto.
    - eapply IHe0_2. apply in_or_app. left. eauto. rewrite <- app_comm_cons in H6. auto.
  * inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
  * inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
    - eapply IHe0_3; eauto.
  * constructor; eauto.
  * constructor.
Qed.

Require Import Sorting.Permutation.

Theorem perm_scoped :
  (forall e Γ Γ', Permutation Γ Γ' -> EXP Γ ⊢ e -> EXP Γ' ⊢ e) /\
  forall e Γ Γ', Permutation Γ Γ' -> VAL Γ ⊢ e -> VAL Γ' ⊢ e.
Proof.
  split. einduction e using Exp_ind2; intros.
  * constructor. constructor.
  * constructor. eapply Permutation_in. exact H. inversion H0. auto. inversion H1.
  * admit.
Admitted.

Theorem scope_ext : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall v, VAL v::Γ ⊢ e) /\
  forall e, EXP Γ ⊢ e -> forall v, EXP v::Γ ⊢ e.
Proof.
  apply scoped_ind.
  * intros. constructor.
  * intros. constructor. apply H.
  * intros. constructor. apply H.
  * intros. constructor. constructor 2. auto.
  * intros. constructor. constructor 2. auto.
  * intros. constructor. apply H. intros. eapply H0. auto.
  * intros. constructor. apply H. apply H0.
  * intros. constructor. apply H. apply H0.
  * intros. constructor. apply H. apply H0.
  * intros. constructor. apply H. apply H0. apply H1.
  * intros. constructor. apply H.
Qed.

Theorem app_cons_swap {T : Type} : forall (l l' : list T) (a : T),
  l ++ a::l' = l ++ [a] ++ l'.
Proof.
  firstorder.
Qed.

Corollary scope_ext_app : forall l Γ,
  (forall e, VAL Γ ⊢ e -> VAL Γ ++ l ⊢ e) /\
  forall e, EXP Γ ⊢ e -> EXP Γ ++ l ⊢ e.
Proof.
 induction l; intros.
 * repeat rewrite app_nil_r. split; intros; auto.
 * rewrite app_cons_swap. pose (scope_ext Γ). specialize (IHl (Γ ++ [a])).
   destruct IHl, a0. split; intros.
   - specialize (H1 e H3 a). eapply perm_scoped in H1. rewrite app_assoc.
     apply H. exact H1. apply Permutation_cons_append.
   - specialize (H2 e H3 a). eapply perm_scoped in H2. rewrite app_assoc.
     apply H0. exact H2. apply Permutation_cons_append.
Qed.

Theorem scope_sub v : forall e,
  (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
  (forall Γ, EXP (inl v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (varsubst v val e)).
Proof.
  einduction e using Exp_ind2 with 
  (Q := fun l => list_forall (fun e => (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
  (forall Γ, EXP (inl v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (varsubst v val e))) l); intros.
  * split; intros; simpl; constructor. constructor.
  * split; intros. inversion H.
    inversion H. 2: inversion H1.
    subst. simpl. break_match_goal.
    - apply eqb_eq in Heqb. subst. simpl. auto.
    - apply eqb_neq in Heqb. inversion H2. inversion H1. congruence.
      constructor. auto.
  * split; intros. inversion H.
    inversion H. 2: inversion H1.
    subst. simpl. inversion H2. inversion H1. constructor. auto.
  * split; intros; inversion H; subst; simpl; break_match_goal; constructor.
    3-4: constructor.
    - apply in_list_sound in Heqb. rewrite <- app_comm_cons in H2.
      eapply scope_duplicate in H2; auto. apply in_app_iff. right. apply in_map. auto.
    - apply IHe0. rewrite <- app_comm_cons in H2. auto.
      eapply scope_ext_app. constructor. auto.
    - apply in_list_sound in Heqb. inversion H1; subst. 
      rewrite <- app_comm_cons in H3.
      eapply scope_duplicate in H3; auto. apply in_app_iff. right. apply in_map. auto.
    - inversion H1. subst. apply IHe0. rewrite app_comm_cons. auto.
      eapply scope_ext_app. auto.
  * split; intros; inversion H; subst; simpl; break_match_goal; constructor.
    3-4: constructor.
    - apply in_list_sound in Heqb. rewrite <- app_comm_cons in H2.
      eapply scope_duplicate in H2; auto. apply in_app_iff. right.
      apply in_app_iff. right. apply in_map. auto.
    - apply IHe0. rewrite <- app_comm_cons in H2. auto.
      eapply scope_ext_app. constructor. auto.
    - apply in_list_sound in Heqb. inversion H1; subst. 
      rewrite <- app_comm_cons in H3.
      eapply scope_duplicate in H3; auto. apply in_app_iff. right.
      apply in_app_iff. right. apply in_map. auto.
    - inversion H1. subst. apply IHe0. rewrite app_comm_cons. auto.
      eapply scope_ext_app. auto.
  * split; intros. inversion H.
    simpl. inversion H. 2: inversion H1. subst. constructor.
    - apply IHe0. auto. auto.
    - rewrite indexed_to_forall in IHe1.
      intros. epose (IHe1 i _). destruct a. clear H2 IHe1. Search map nth.
      replace (ELit 0) with ((varsubst v val) (ELit 0)). rewrite map_nth. apply H5.
      apply H4. rewrite map_length in H1. auto. auto. reflexivity.
  * split; intros; inversion H; subst.
    - simpl. break_match_goal.
      + apply eqb_eq in Heqb. subst. constructor. apply IHe0_1; eauto.
        apply scope_duplicate in H5. 2: apply in_or_app; right; constructor; auto.
        exact H5.
      + apply eqb_neq in Heqb. constructor.
        apply IHe0_1; eauto.
        apply IHe0_2; eauto.
        eapply scope_ext_app in H0. eauto.
    - inversion H1.
  * split; intros. inversion H. subst.
    simpl. inversion H. 2: inversion H1. subst. break_match_goal.
    - constructor. rewrite <- app_comm_cons in H3. eapply scope_duplicate.
      2: exact H3. apply in_list_sound in Heqb. apply in_app_iff. right.
      apply in_app_iff. right.
      apply in_map. auto.
      apply IHe0_2. rewrite <- app_comm_cons in H6. auto.
      eapply scope_ext_app in H0. eauto.
    - constructor.
      apply IHe0_1; eauto. eapply scope_ext_app. eauto.
      apply IHe0_2; eauto. eapply scope_ext_app. eauto.
  * split; intros. inversion H. subst. simpl. inversion H. 2: inversion H1. subst.
    constructor. 
    eapply IHe0_1; auto. eapply IHe0_2; auto.
  * split; intros. inversion H. subst. simpl. inversion H. 2: inversion H1. subst.
    constructor. 
    eapply IHe0_1; auto. eapply IHe0_2; auto. eapply IHe0_3; auto.
  * constructor. apply IHe0. apply IHe1.
  * constructor.
Unshelve. rewrite map_length in H1. auto.
Qed.

Theorem scope_funsub v : forall e,
  (forall Γ, VAL (inr v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (funsubst v val e)) /\
  (forall Γ, EXP (inr v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (funsubst v val e)).
Proof.
  einduction e using Exp_ind2 with 
  (Q := fun l => list_forall (fun e => (forall Γ, VAL (inr v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (funsubst v val e)) /\
  (forall Γ, EXP (inr v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (funsubst v val e))) l); intros.
  * split; intros; simpl; constructor. constructor.
  * split; intros. inversion H.
    inversion H. 2: inversion H1. simpl. subst. constructor.
    inversion H2. inversion H1. auto.
  * split; intros; simpl; break_match_goal; auto. inversion H. constructor.
    inversion H. 2: inversion H1. subst. apply funid_eqb_neq in Heqb. inversion H2.
    - inversion H1. subst. congruence.
    - auto.
  * split; intros; inversion H; subst; simpl; constructor. 2: constructor.
    - apply IHe0. rewrite app_comm_cons. auto. apply scope_ext_app. constructor. auto.
    - inversion H1. subst. apply IHe0. rewrite app_comm_cons. auto.
      apply scope_ext_app. auto.
  * split; intros; inversion H; subst; simpl; break_match_goal.
    - apply funid_eqb_eq in Heqb. subst. constructor. rewrite <- app_comm_cons in H2.
      eapply scope_duplicate. 2: exact H2.
      apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
    - constructor. apply IHe0. rewrite app_comm_cons. auto.
      apply scope_ext_app. constructor. auto.
    - inversion H1. subst. apply funid_eqb_eq in Heqb. subst.
      constructor. constructor. rewrite <- app_comm_cons in H3.
      eapply scope_duplicate. 2: exact H3.
      apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
    - constructor. constructor. inversion H1. subst.
      apply IHe0. rewrite app_comm_cons. auto.
      apply scope_ext_app. auto.
  * split; intros. inversion H.
    simpl. inversion H. 2: inversion H1. subst. constructor.
    - apply IHe0. auto. auto.
    - rewrite indexed_to_forall in IHe1.
      intros. epose (IHe1 i _). destruct a. clear H2 IHe1. Search map nth.
      replace (ELit 0) with ((funsubst v val) (ELit 0)). rewrite map_nth. apply H5.
      apply H4. rewrite map_length in H1. auto. auto. reflexivity.
  * split; intros; inversion H; subst.
    - simpl. constructor.
      apply IHe0_1; eauto.
      apply IHe0_2; eauto.
      eapply scope_ext_app in H0. eauto.
    - inversion H1.
  * split; intros; inversion H. subst.
    simpl. break_match_goal.
    - constructor. apply funid_eqb_eq in Heqb. subst. rewrite <- app_comm_cons in H3.
      eapply scope_duplicate. 2: exact H3. apply in_app_iff. right.
      apply in_app_iff. left. constructor. auto.
      apply funid_eqb_eq in Heqb. subst. rewrite <- app_comm_cons in H6.
      eapply scope_duplicate. 2: exact H6. apply in_app_iff. intuition.
    - apply funid_eqb_neq in Heqb. constructor.
      apply IHe0_1. try rewrite app_comm_cons; eauto.
      apply scope_ext_app. auto.
      apply IHe0_2. rewrite app_comm_cons; auto.
      apply scope_ext_app. auto.
    - inversion H1.
  * split; intros. inversion H. subst. simpl. inversion H. 2: inversion H1. subst.
    constructor. 
    eapply IHe0_1; auto. eapply IHe0_2; auto.
  * split; intros. inversion H. subst. simpl. inversion H. 2: inversion H1. subst.
    constructor. 
    eapply IHe0_1; auto. eapply IHe0_2; auto. eapply IHe0_3; auto.
  * constructor. apply IHe0. apply IHe1.
  * constructor.
Unshelve. rewrite map_length in H1. auto.
Qed.

Corollary scope_subst v : forall e,
  (forall Γ, VAL (v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (subst v val e)) /\
  (forall Γ, EXP (v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (subst v val e)).
Proof.
  destruct v.
  - apply scope_sub.
  - apply scope_funsub.
Qed.

Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Corollary scope_subst_list Γ : forall e,
  (VAL Γ ⊢ e -> forall vals, length vals = length Γ -> subscoped [] vals -> VAL Γ ⊢ (subst_list Γ vals e)) /\
  (EXP Γ ⊢ e -> forall vals, length vals = length Γ -> subscoped [] vals -> EXP Γ ⊢ (subst_list Γ vals e)).
Proof.
  induction Γ; split; intros.
  * unfold subst_list. simpl. auto.
  * unfold subst_list. simpl. auto.
  * unfold subscoped in H1. apply eq_sym, element_exist in H0 as EE. destruct EE, H2.
    subst. unfold subst_list. simpl.
    replace (fold_left (fun (acc : Exp) '(v, val) => subst v val acc) (combine Γ x0) (subst a x e)) with (subst_list Γ x0 (subst a x e)). 2: reflexivity.
    specialize (IHΓ (subst a x e)). destruct IHΓ.
    inversion H0.
    epose (H2 _ x0 (eq_sym H5) _). apply scope_ext. auto.
  * unfold subscoped in H1. apply eq_sym, element_exist in H0 as EE. destruct EE, H2.
    subst. unfold subst_list. simpl.
    replace (fold_left (fun (acc : Exp) '(v, val) => subst v val acc) (combine Γ x0) (subst a x e)) with (subst_list Γ x0 (subst a x e)). 2: reflexivity.
    specialize (IHΓ (subst a x e)). destruct IHΓ.
    inversion H0.
    epose (H3 _ x0 (eq_sym H5) _). apply scope_ext. auto.
Unshelve.
  - apply scope_subst; eauto. specialize (H1 0 (Nat.lt_0_succ _)).
    simpl in H1. replace Γ with ([] ++ Γ); auto. apply scope_ext_app. auto.
  - intro. intros. apply (H1 (S i)). simpl. lia.
  - apply scope_subst; eauto. specialize (H1 0 (Nat.lt_0_succ _)).
    simpl in H1. replace Γ with ([] ++ Γ); auto. apply scope_ext_app. auto.
    constructor. auto.
  - intro. intros. apply (H1 (S i)). simpl. lia.
Qed.

(* Lemma VarFunId_eq_dec (v v' : VarFunId) : {v = v'} + {v <> v'}.
Proof. decide equality. apply string_dec. repeat decide equality. Qed. *)

Fixpoint mem {E : Type} (eqb : E -> E -> bool) (e : E) (l : list E) :=
match l with
| [] => false
| x::xs => if eqb x e then true else mem eqb e xs
end.

Compute mem var_funid_eqb (inl "X"%string) [inl "X"%string].

Theorem mem_sound : forall l e, mem var_funid_eqb e l = true <-> In e l.
Proof.
  induction l; intros.
  * split; intros; inversion H.
  * split; intros.
    - simpl in H. break_match_hyp.
      + apply var_funid_eqb_eq in Heqb. simpl. left. auto.
      + apply var_funid_eqb_neq in Heqb. simpl. right. apply IHl. auto.
    - destruct (var_funid_eqb a e) eqn:P.
      + apply var_funid_eqb_eq in P. subst. simpl. rewrite var_funid_eqb_refl. auto.
      + simpl. rewrite P. apply IHl. inversion H.
        ** apply var_funid_eqb_neq in P. congruence.
        ** auto.
Qed.

Fixpoint subst_free (e' : Exp) (ξ : VarFunId -> Exp) (l : list VarFunId) : Exp :=
match e' with
 | ELit l => ELit l
 | EVar v => if mem var_funid_eqb (inl v) l then EVar v else ξ (inl v)
 | EFunId f => if mem var_funid_eqb (inr f) l then EFunId f else ξ (inr f)
 | EFun vl e => EFun vl (subst_free e ξ (l ++ map inl vl))
 | ERecFun f vl e => ERecFun f vl (subst_free e ξ (l ++ [inr f] ++ map inl vl))
 | EApp exp l' => EApp (subst_free exp ξ l) (map (fun x => subst_free x ξ l) l')
 | ELet v e1 e2 => ELet v (subst_free e1 ξ l) (subst_free e2 ξ (l ++ [inl v]))
 | ELetRec f vl b e => ELetRec f vl (subst_free b ξ (l ++ [inr f] ++ map inl vl)) (subst_free e ξ (l ++ [inr f]))
 | EPlus e1 e2 => EPlus (subst_free e1 ξ l) (subst_free e2 ξ l)
 | EIf e1 e2 e3 => EIf  (subst_free e1 ξ l) (subst_free e2 ξ l) (subst_free e3 ξ l)
end.

Notation "e [[ ξ ]]" := (subst_free e ξ []) (at level 5).


Definition Vrel_open (Γ : list VarFunId) (e1 e2 : Exp) :=
  forall n ξ η,
  Grel n Γ ξ η ->
  Vrel n e1[[ξ]] e2[[η]].

Definition Erel_open (Γ : list VarFunId) (e1 e2 : Exp) :=
  forall n ξ η,
  Grel n Γ ξ η ->
  Erel n e1[[ξ]] e2[[η]].

Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Lemma Vrel_Var_compatible :
  forall Γ x,
    In (inl x) Γ ->
    Vrel_open Γ (EVar x) (EVar x).
Proof.
  unfold Vrel_open, Grel.
  cbn. (* intros. destruct H0, H1. apply H2. auto. *)
  intuition.
Qed.

Hint Resolve Vrel_Var_compatible.

Lemma Vrel_FunId_compatible :
  forall Γ x,
    In (inr x) Γ ->
    Vrel_open Γ (EFunId x) (EFunId x).
Proof.
  unfold Vrel_open, Grel.
  cbn.
  intuition.
Qed.

Hint Resolve Vrel_FunId_compatible.

Lemma Erel_Var_compatible :
  forall Γ x,
    In (inl x) Γ ->
    Erel_open Γ (EVar x) (EVar x).
Proof.
  unfold Erel_open, Grel.
  cbn. (* intros. destruct H0, H1. apply H2. auto. *)
  intuition. specialize (H3 _ H).
  unfold Erel, exp_rel. split. 2: split. 1-2: admit. intros. apply H3. 
Qed.

Hint Resolve Vrel_Var_compatible.

Lemma Vrel_FunId_compatible :
  forall Γ x,
    In (inr x) Γ ->
    Erel_open Γ (EFunId x) (EFunId x).
Proof.
  unfold Vrel_open, Grel.
  cbn.
  intuition.
Qed.

Hint Resolve Vrel_FunId_compatible.

Lemma Vrel_Lit_compatible_closed :
  forall m r,
    Vrel m (ELit r) (ELit r).
Proof.
  intros.
  rewrite Vrel_Fix_eq.
  unfold Vrel_rec.
  intuition constructor.
Qed.

Hint Resolve Vrel_Lit_compatible_closed.

Lemma Vrel_Lit_compatible :
  forall Γ r,
    Vrel_open Γ (ELit r) (ELit r).
Proof.
  unfold Vrel_open, Grel.
  intros.
  cbn.
  apply Vrel_Lit_compatible_closed.
Qed.

Hint Resolve Vrel_Lit_compatible.


Theorem Erel_Vrel_Fundamental_helper :
  forall (e : Exp),
    (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
    (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e).
Proof.
  induction e;
    intuition auto;
    try solve_inversion.
  - eapply 
  - eapply Erel_App_compatible; eauto.
  - eapply Erel_Seq_compatible; eauto.
  - eapply Erel_Op1_compatible; eauto.
  - eapply Erel_Op2_compatible; eauto.
  - eapply Erel_Cond_compatible; eauto.
Qed.





Lemma Erel_open_closed : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    forall γ, subscoped Γ [] γ ->
              EXPCLOSED (e1[[γ]]) /\ EXPCLOSED (e2[[γ]]).
Proof.
  
Qed.

Lemma Erel_open_closed : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    forall γ, subscoped Γ [] γ ->
              EXPCLOSED (e1[[γ]]) /\ EXPCLOSED (e2[[γ]]).
Proof.
  intros.
  apply @Erel_closed with (n:=0).
  apply H.
  unfold Grel.
  intuition idtac.
  pose (E := H0 x H1). rewrite Vrel_Fix_eq. inversion E. 
  unfold Vrel_rec. split. 2: split; auto. 1-2: constructor.
  
  
  remember E as E'. clear HeqE' E.
  break_match_goal; auto. 1-2, 5-9: inversion E'.
  break_match_goal; try congruence; intros.
  
  
  
  
  unfold Vrel_rec at 1; intuition.
  break_match_goal; auto; try inversion E'.
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

(* 
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
*)
