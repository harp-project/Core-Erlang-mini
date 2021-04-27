Require Export SubstSemantics.
Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FunctionalExtensionality.

Import ListNotations.

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

Theorem not_in_list_sound : forall l e, in_list e l = false <-> ~In e l.
Proof.
  induction l; intros.
  * split; intros. intro. inversion H0. reflexivity.
  * split; intros.
    - simpl in H. break_match_hyp.
      + inversion H.
      + apply var_funid_eqb_neq in Heqb. simpl. intro. inversion H0. symmetry in H1. contradiction.
        eapply IHl; eauto.
    - simpl. break_match_goal.
      apply var_funid_eqb_eq in Heqb. subst. exfalso. apply H. intuition.
      apply var_funid_eqb_neq in Heqb. eapply IHl. apply not_in_cons in H. destruct H. auto.
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


Reserved Notation "'EXP' Γ ⊢ e"
         (at level 69, no associativity).

Reserved Notation "'VAL' Γ ⊢ v"
         (at level 69, no associativity).
Inductive ExpScoped (l : list VarFunId) : Exp -> Prop :=
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
  EXP (l ++ inr f :: map inl vl) ⊢ b -> EXP (l ++ [inr f]) ⊢ e
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
| scoped_var v : In (inl v) l -> VAL l ⊢ EVar v
| scoped_funid f : In (inr f) l -> VAL l ⊢ EFunId f
| scoped_fun vl e : EXP (l ++ (map inl vl)) ⊢ e -> VAL l ⊢ EFun vl e
| scoped_recfun f vl e : EXP (l ++ inr f :: map inl vl) ⊢ e -> VAL l ⊢ ERecFun f vl e
where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)
and "'VAL' Γ ⊢ e" := (ValScoped Γ e).

Notation "'EXPCLOSED' e" := (EXP [] ⊢ e) (at level 5).
Notation "'VALCLOSED' v" := (VAL [] ⊢ v) (at level 5).

Scheme ValScoped_ind2 := Induction for ValScoped Sort Prop
  with ExpScoped_ind2 := Induction for ExpScoped Sort Prop.
Combined Scheme scoped_ind from ValScoped_ind2, ExpScoped_ind2.
Check scoped_ind.

Definition subst_preserves (Γ : list VarFunId) (ξ : Substitution) : Prop :=
  forall v, In v Γ -> ξ v = idsubst v.

Theorem subst_preserves_removed : forall Γ l ξ,
  subst_preserves Γ ξ -> subst_preserves (Γ ++ l) (ξ -- l).
Proof.
  intros. intro. intros. apply in_app_iff in H0. destruct H0.
  * unfold "--". break_match_goal. auto. apply H. auto.
  * unfold "--". break_match_goal; auto. apply not_in_list_sound in Heqb.
    contradiction. (* TODO: rewrite fails here, I do not know why *)
Qed.

Hint Resolve subst_preserves_removed.

Theorem subst_preserves_empty ξ : subst_preserves [] ξ.
Proof. intro. intros. inversion H. Qed.

Hint Resolve subst_preserves_empty.

Theorem scoped_ignores_sub_helper vals : forall l ξ,
  (forall i : nat,
     i < Datatypes.length vals ->
     forall ξ : Substitution,
     subst_preserves l ξ -> subst ξ (nth i vals (ELit 0)) = nth i vals (ELit 0)) ->
  subst_preserves l ξ ->
  (map (subst ξ) vals) = vals.
Proof.
  induction vals; intros.
  * reflexivity.
  * simpl. epose (H 0 _ _ H0). simpl in e. rewrite e.
    erewrite IHvals; eauto. intros. eapply (H (S i)). simpl. lia. auto.
Unshelve. simpl. lia.
Qed.

Theorem scoped_ignores_sub : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> subst ξ e = e) /\
  (forall e, EXP Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> subst ξ e = e).
Proof.
  apply scoped_ind.
  * intros. reflexivity.
  * intros. simpl. apply H in i. simpl in i. auto.
  * intros. simpl. apply H in i. simpl in i. auto.
  * intros. simpl. epose (H _ _). rewrite e1. reflexivity.
    Unshelve. apply subst_preserves_removed. apply H0.
  * intros. simpl. epose (H _ _). rewrite e1. reflexivity.
    Unshelve. auto.
  * intros. simpl. rewrite H; auto. erewrite scoped_ignores_sub_helper; eauto.
  * intros. simpl. rewrite H; auto. rewrite H0; auto.
  * intros. simpl. rewrite H, H0; auto.
  * intros. simpl. rewrite H, H0; auto.
  * intros. simpl. rewrite H, H0, H1; auto.
  * intros. eapply H; eauto.
Qed.

Corollary eclosed_ignores_sub :
  forall e ξ,
  EXPCLOSED e -> subst ξ e = e.
Proof.
  intros. eapply scoped_ignores_sub with (Γ := []); auto.
Qed.

Corollary vclosed_ignores_sub :
  forall e ξ,
  VALCLOSED e -> subst ξ e = e.
Proof.
  intros. pose (scoped_ignores_sub []). destruct a. apply H0; auto.
Qed.

Theorem scope_duplicate e :
  (forall Γ v, In v Γ -> EXP (v :: Γ) ⊢ e -> EXP Γ ⊢ e) /\
  (forall Γ v, In v Γ -> VAL (v :: Γ) ⊢ e -> VAL Γ ⊢ e).
Proof.
  einduction e using Exp_ind2 with 
      (Q := fun l => Forall (fun e => 
        (forall Γ v, In v Γ -> EXP (v :: Γ) ⊢ e -> EXP Γ ⊢ e) /\
        (forall Γ v, In v Γ -> VAL (v :: Γ) ⊢ e -> VAL Γ ⊢ e)) l); intros.
  * repeat constructor.
  * split; intros.
    - inversion H0. subst. inversion H1. constructor. inversion H3; subst;
      constructor; auto.
    - inversion H0. inversion H2; subst; constructor; auto.
  * split; intros. 
    - inversion H0. subst. inversion H1. inversion H3; constructor; subst;
      constructor; auto.
    - inversion H0. inversion H2; subst; constructor; auto.
  * split; intros. 
    - constructor. constructor. inversion H0. inversion H1. subst.
      rewrite <- app_comm_cons in H4. apply IHe0 in H4; auto. apply in_or_app. left.
      auto.
    - constructor. inversion H0. subst.
      rewrite <- app_comm_cons in H2. apply IHe0 in H2; auto. apply in_or_app. left.
      auto.
  * split; intros. 
    - constructor. constructor. inversion H0. inversion H1. subst.
      rewrite <- app_comm_cons in H4. apply IHe0 in H4; auto. apply in_or_app. left.
      auto.
    - constructor. inversion H0. subst.
      rewrite <- app_comm_cons in H2. apply IHe0 in H2; auto. apply in_or_app. left.
      auto.
  * split; intros; inversion H0. 2: inversion H1. subst. rewrite indexed_to_forall in IHe1.
    constructor.
    - eapply IHe0; eauto.
    - intros. eapply IHe1; eauto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. exact H. auto.
    - rewrite <- app_comm_cons in H5. eapply IHe0_2. 2: exact H5.
      apply in_or_app. left. auto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. apply in_or_app. left. eauto. rewrite <- app_comm_cons in H3. auto.
    - eapply IHe0_2. apply in_or_app. left. eauto. rewrite <- app_comm_cons in H6. auto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
    - eapply IHe0_3; eauto.
  * constructor; eauto.
  * constructor.
Qed.

Require Import Sorting.Permutation.

Theorem perm_scoped : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall Γ', Permutation Γ Γ' -> VAL Γ' ⊢ e) /\
  (forall e, EXP Γ ⊢ e -> forall Γ', Permutation Γ Γ' ->  EXP Γ' ⊢ e).
Proof.
  apply scoped_ind; intros; constructor; intuition.
  1-2: eapply Permutation_in; eauto.
  all: apply H0 || apply H; apply Permutation_app; intuition.
Qed.

Theorem scope_ext : forall Γ,
  (forall e, VAL Γ ⊢ e -> forall v, VAL v::Γ ⊢ e) /\
  forall e, EXP Γ ⊢ e -> forall v, EXP v::Γ ⊢ e.
Proof.
  apply scoped_ind; intros; constructor; try constructor 2; auto;
    try apply H; try apply H0; try apply H1.
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

(*
Theorem scope_subst v : forall e,
  (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
  (forall Γ, EXP (inl v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (varsubst v val e)).
Proof.
  einduction e using Exp_ind2 with 
  (Q := fun l => Forall (fun e => (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
  (forall Γ, EXP (inl v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (varsubst v val e))) l); intros.
  * split; intros; simpl; constructor. constructor.
  * split; intros;
    subst; simpl; break_match_goal.
    - apply eqb_eq in Heqb. subst. simpl. auto.
    - apply eqb_neq in Heqb. inversion H. inversion H2. congruence.
      constructor. auto.
    - apply eqb_eq in Heqb. subst. simpl. auto.
    - apply eqb_neq in Heqb. inversion H. inversion H1. inversion H4. congruence.
      constructor. constructor. auto.
  * split; intros. inversion H.
    - subst. simpl. inversion H2. inversion H1. constructor. auto.
    - subst. simpl. inversion H. inversion H1. constructor. constructor.
      inversion H4; auto. congruence.
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
  (Q := fun l => Forall (fun e => (forall Γ, VAL (inr v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (funsubst v val e)) /\
  (forall Γ, EXP (inr v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (funsubst v val e))) l); intros.
  * split; intros; simpl; constructor. constructor.
  * split; intros. inversion H.
    inversion H2. congruence. simpl. subst. constructor. auto.
    inversion H. inversion H1. inversion H4. congruence.
      simpl. constructor. constructor. auto.
  * split; intros; simpl; break_match_goal; auto. 
    - inversion H. constructor.
      inversion H2. subst. apply funid_eqb_neq in Heqb. inversion H3. subst. congruence. auto.
    - inversion H. inversion H1. subst. inversion H4. inversion H2. subst.
      rewrite funid_eqb_refl in Heqb. congruence.
      constructor. constructor. auto.
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
*)
Theorem scope_duplicate_rev e :
  (forall Γ v, In v Γ -> EXP Γ ⊢ e -> EXP v::Γ ⊢ e) /\
  (forall Γ v, In v Γ -> VAL Γ ⊢ e -> VAL v::Γ ⊢ e).
Proof.
  einduction e using Exp_ind2 with 
      (Q := fun l => Forall (fun e => 
        (forall Γ v, In v Γ -> EXP Γ ⊢ e -> EXP (v::Γ) ⊢ e) /\
        (forall Γ v, In v Γ -> VAL Γ ⊢ e -> VAL (v::Γ) ⊢ e)) l); intros.
  * repeat constructor.
  * split; intros.
    - inversion H0. subst. constructor. constructor. constructor 2.
      inversion H1. auto.
    - inversion H0. constructor. constructor 2. subst. auto.
  * split; intros. 
    - inversion H0. subst. constructor. constructor. constructor 2.
      inversion H1. auto.
    - inversion H0. constructor. constructor 2. subst. auto.
  * split; intros. 
    - constructor. constructor. inversion H0. inversion H1. subst.
      rewrite <- app_comm_cons. apply IHe0; auto. apply in_or_app. left.
      auto.
    - constructor. inversion H0. subst.
      rewrite <- app_comm_cons. apply IHe0; auto. apply in_or_app. left.
      auto.
  * split; intros. 
    - constructor. constructor. inversion H0. inversion H1. subst.
      rewrite <- app_comm_cons . apply IHe0; auto. apply in_or_app. left.
      auto.
    - constructor. inversion H0. subst.
      rewrite <- app_comm_cons. apply IHe0; auto. apply in_or_app. left.
      auto.
  * split; intros; inversion H0. 2: inversion H1. subst. rewrite indexed_to_forall in IHe1.
    constructor.
    - eapply IHe0; eauto.
    - intros. eapply IHe1; eauto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. exact H. auto.
    - rewrite <- app_comm_cons. eapply IHe0_2. 2: exact H5.
      apply in_or_app. left. auto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1. apply in_or_app. left. eauto. auto.
    - rewrite <- app_comm_cons. eapply IHe0_2. apply in_or_app. left. eauto. auto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
  * split; intros; inversion H0. 2: inversion H1. subst. constructor.
    - eapply IHe0_1; eauto.
    - eapply IHe0_2; eauto.
    - eapply IHe0_3; eauto.
  * constructor; eauto.
  * constructor.
Qed.
(* 
Corollary scope_subst_in v : forall e,
  (forall Γ, In v Γ -> 
    VAL Γ ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (subst v val e)) /\
  (forall Γ, In v Γ ->
    EXP Γ ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (subst v val e)).
Proof.
  intros; split; intros.
  * apply scope_subst; auto. eapply scope_duplicate_rev in H; eauto.
  * apply scope_subst; auto. pose (scope_duplicate_rev e). destruct a. apply H2; eauto.
Qed. *)

Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Definition subscoped (l l' : list VarFunId) (ξ : Substitution) : Prop :=
  forall v, In v l -> VAL l' ⊢ ξ v.

(* Corollary scope_subst_list Γ' : forall Γ e,
  (VAL (Γ ++ Γ') ⊢ e -> forall vals, length vals = length Γ' -> subscoped Γ vals -> VAL Γ ⊢ (subst_list Γ' vals e)) /\
  (EXP (Γ ++ Γ') ⊢ e -> forall vals, length vals = length Γ' -> subscoped Γ vals -> EXP Γ ⊢ (subst_list Γ' vals e)).
Proof.
  induction Γ'; split; intros.
  1-2: rewrite app_nil_r in H; unfold subst_list; simpl; auto.
  * unfold subscoped in H1. apply eq_sym, element_exist in H0 as EE. destruct EE, H2.
    subst. unfold subst_list. simpl.
    replace (fold_left (fun (acc : Exp) '(v, val) => subst v val acc) (combine Γ' x0) (subst a x e)) with (subst_list Γ' x0 (subst a x e)). 2: reflexivity.
    specialize (IHΓ' Γ (subst a x e)). destruct IHΓ'.
    inversion H0.
    epose (H2 _ x0 (eq_sym H5) _). auto.
  * unfold subscoped in H1. apply eq_sym, element_exist in H0 as EE. destruct EE, H2.
    subst. unfold subst_list. simpl.
    replace (fold_left (fun (acc : Exp) '(v, val) => subst v val acc) (combine Γ' x0) (subst a x e)) with (subst_list Γ' x0 (subst a x e)). 2: reflexivity.
    specialize (IHΓ' Γ (subst a x e)). destruct IHΓ'.
    inversion H0.
    epose (H3 _ x0 (eq_sym H5) _). auto.
Unshelve.
  2, 4: intro; intros; apply (H1 (S i)); simpl; lia.
  - apply scope_subst; eauto.
    + eapply perm_scoped. exact H. apply Permutation_sym, Permutation_middle.
    + specialize (H1 0 (Nat.lt_0_succ _)).
      simpl in H1. apply scope_ext_app. auto.
  - apply scope_subst; eauto.
    + eapply perm_scoped. exact H. apply Permutation_sym, Permutation_middle.
    + specialize (H1 0 (Nat.lt_0_succ _)).
      simpl in H1. apply scope_ext_app. auto. constructor. auto.
Qed.


Corollary scope_subst_list_closed Γ : forall e,
  (VAL Γ ⊢ e -> forall vals, length vals = length Γ -> subscoped [] vals -> VALCLOSED (subst_list Γ vals e)) /\
  (EXP Γ ⊢ e -> forall vals, length vals = length Γ -> subscoped [] vals -> EXPCLOSED (subst_list Γ vals e)).
Proof.
  intros. pose (scope_subst_list Γ []). simpl in a. auto.
Qed. *)
Fixpoint create_list (e : Exp) (n : nat) :=
match n with
| 0 => []
| S n' => e :: create_list e n'
end.

Theorem subst_in :
  forall ξ e v, ξ[[ v ::= e ]] v = e.
Proof. intros. unfold extend_subst. rewrite var_funid_eqb_refl. auto. Qed.

Theorem subst_not_in :
  forall ξ e v v', v' <> v -> ξ[[ v' ::= e ]] v = ξ v.
Proof.
  intros. unfold extend_subst. apply var_funid_eqb_neq in H.
  rewrite H. auto.
Qed.

(* Corollary subst_in_list :
  forall l ξ v e, In (v, e) l -> ξ[[ ::= l]] v = e.
Proof.
  induction l; intros.
  * inversion H.
  * unfold extend_subst_list. simpl. destruct a.
    replace (fold_right (fun '(x, e1) (ξ' : Substitution) => ξ' [[x ::= e1]]) ξ l [[v0 ::= e0]]) with (ξ[[ ::= l]][[v0 ::= e0]]) by reflexivity.
    epose (var_funid_eq_dec v v0).
    destruct s.
    - inversion e1. subst. apply subst_in. 
    - inversion H.
      + congruence.
      + rewrite subst_not_in; auto. apply IHl.
Qed. *)

Theorem var_not_closed1 v : ~ VALCLOSED (EVar v).
Proof. intro. inversion H. inversion H1. Qed.

Hint Resolve var_not_closed1.

Theorem var_not_closed2 v : ~ EXPCLOSED (EVar v).
Proof. intro. inversion H. eapply var_not_closed1. eauto. Qed.

Hint Resolve var_not_closed2.

Theorem funid_not_closed1 v : ~ VALCLOSED (EFunId v).
Proof. intro. inversion H. inversion H1. Qed.

Hint Resolve funid_not_closed1.

Theorem funid_not_closed2 v : ~ EXPCLOSED (EFunId v).
Proof. intro. inversion H. eapply funid_not_closed1. eauto. Qed.

Hint Resolve funid_not_closed2.

Theorem restrict_in : forall l ξ v,
  In v l -> (ξ -- l) v = idsubst v.
Proof.
  intros. unfold "--". apply in_list_sound in H. rewrite H. auto.
Qed.

Theorem restrict_not_in : forall l ξ v,
  ~In v l -> (ξ -- l) v = ξ v.
Proof.
  intros. unfold "--". apply not_in_list_sound in H. rewrite H. auto.
Qed.

Theorem subscoped_preserves_app : forall ξ Γ Γ',
  subscoped Γ Γ' ξ -> (forall l, subscoped (Γ ++ l) (Γ' ++ l) (ξ -- l)).
Proof.
  intros. intro. intros. destruct (in_dec var_funid_eq_dec v l) eqn:P.
  * rewrite restrict_in by auto. unfold idsubst.
    destruct v; constructor; apply in_app_iff; right; auto.
  * rewrite restrict_not_in by auto.
    apply scope_ext_app. unfold subscoped in H. apply H.
    apply in_app_iff in H0. destruct H0; auto. congruence.
Qed.

Hint Resolve subscoped_preserves_app.

Corollary subscoped_ext :
  forall ξ Γ Γ' l, subscoped (Γ ++ l) Γ' ξ -> subscoped Γ Γ' ξ.
Proof.
  unfold subscoped. intros. intuition.
Qed.

Theorem subst_restrict_comm : forall ξ l1 l2,
  (ξ -- l1 -- l2) = (ξ -- l2 -- l1).
Proof.
  intros. unfold "--". extensionality x.
  repeat break_match_goal; auto.
Qed.

Theorem subst_remove_scope : forall e Γ ξ l,
  (EXP Γ ⊢ subst ξ e -> EXP Γ ++ l ⊢ subst (ξ -- l) e) /\
  (VAL Γ ⊢ subst ξ e -> VAL Γ ++ l ⊢ subst (ξ -- l) e).
Proof.
  induction e using Exp_ind2 with 
    (Q := fun l => Forall (fun e => forall Γ ξ l,
  (EXP Γ ⊢ subst ξ e -> EXP Γ ++ l ⊢ subst (ξ -- l) e) /\
  (VAL Γ ⊢ subst ξ e -> VAL Γ ++ l ⊢ subst (ξ -- l) e)) l)
  ; try split; intros.
  * repeat constructor.
  * repeat constructor.
  * unfold subst. destruct (in_dec var_funid_eq_dec (inl v) l) eqn:P.
    - rewrite restrict_in by auto. simpl. constructor. constructor. intuition.
    - rewrite restrict_not_in by auto. unfold subst in H. apply scope_ext_app. auto.
  * unfold subst. destruct (in_dec var_funid_eq_dec (inl v) l) eqn:P.
    - rewrite restrict_in by auto. simpl. constructor. intuition.
    - rewrite restrict_not_in by auto. unfold subst in H. apply scope_ext_app. auto.
  * unfold subst. destruct (in_dec var_funid_eq_dec (inr f) l) eqn:P.
    - rewrite restrict_in by auto. simpl. constructor. constructor. intuition.
    - rewrite restrict_not_in by auto. unfold subst in H. apply scope_ext_app. auto.
  * unfold subst. destruct (in_dec var_funid_eq_dec (inr f) l) eqn:P.
    - rewrite restrict_in by auto. simpl. constructor. intuition.
    - rewrite restrict_not_in by auto. unfold subst in H. apply scope_ext_app. auto.
  * simpl. constructor. constructor.
    rewrite <- app_assoc. pose (perm_scoped (Γ ++ map inl vl ++ l)). destruct a.
    clear H0. apply H1. rewrite subst_restrict_comm. rewrite app_assoc. apply IHe.
    inversion H. inversion H0. subst. auto.
    apply Permutation_app; auto. apply Permutation_app_comm.
  * simpl. constructor.
    rewrite <- app_assoc. pose (perm_scoped (Γ ++ map inl vl ++ l)). destruct a.
    clear H0. apply H1. rewrite subst_restrict_comm. rewrite app_assoc. apply IHe.
    inversion H. subst. auto.
    apply Permutation_app; auto. apply Permutation_app_comm.
  * simpl. constructor. constructor.
    rewrite <- app_assoc. pose (perm_scoped (Γ ++ (inr f :: map inl vl) ++ l)).
    destruct a.
    clear H0. apply H1. rewrite subst_restrict_comm. rewrite app_assoc. apply IHe.
    inversion H. inversion H0. subst. auto.
    apply Permutation_app; auto. apply Permutation_app_comm.
  * simpl. constructor.
    rewrite <- app_assoc. pose (perm_scoped (Γ ++ (inr f :: map inl vl) ++ l)).
    destruct a.
    clear H0. apply H1. rewrite subst_restrict_comm. rewrite app_assoc. apply IHe.
    inversion H. subst. auto.
    apply Permutation_app; auto. apply Permutation_app_comm.
  * inversion H. 2: inversion H0. simpl. constructor.
    - apply IHe. auto.
    - rewrite indexed_to_forall in IHe0. intros.
      replace (ELit 0) with (subst (ξ -- l) (ELit 0)) by reflexivity.
      rewrite map_nth. apply IHe0. rewrite map_length in H4. auto.
      rewrite map_length in H4. erewrite <- map_length in H4. specialize (H3 i H4).
      replace (ELit 0) with (subst ξ (ELit 0)) in H3 by reflexivity.
      rewrite map_nth in H3. auto.
  * inversion H.
  * inversion H. 2: inversion H0. subst.
    simpl. constructor.
    - apply IHe1. auto.
    - rewrite <- app_assoc. eapply perm_scoped. rewrite subst_restrict_comm.
      apply IHe2. eauto.
      rewrite <- app_assoc. apply Permutation_app; auto. apply Permutation_app_comm.
  * inversion H.
  * inversion H. 2: inversion H0. subst.
    simpl. constructor; rewrite subst_restrict_comm.
    - rewrite <- app_assoc. eapply perm_scoped. apply IHe1. eauto.
      rewrite <- app_assoc. apply Permutation_app; auto. apply Permutation_app_comm.
    - rewrite <- app_assoc. eapply perm_scoped. apply IHe2. eauto.
      rewrite <- app_assoc. apply Permutation_app; auto. apply Permutation_app_comm.
  * inversion H.
  * inversion H. subst. simpl.
    constructor; [ apply IHe1 | apply IHe2 ]; auto.
    inversion H0.
  * inversion H.
  * inversion H. subst. simpl.
    constructor; [ apply IHe1 | apply IHe2 | apply IHe3 ]; auto.
    inversion H0.
  * inversion H.
  * constructor; eauto.
  * constructor.
Qed.

Definition vals_subscoped vals Γ :=
  forall v, In v vals -> VAL Γ ⊢ v
.

(* 
!!!!!!!!!!!!!
This does not hold: 

Theorem ex_subst_exp :
  forall e ξ l vals, subst (ξ[[ l ::== vals ]]) e =
              subst (idsubst [[l ::== vals]]) (subst ξ e).
Proof.
  intros. induction e.
  * simpl. reflexivity.
  * simpl. *)
(*
This does not hold:

bc. e ::= EVar v
    Γ ::= [v]
    l ::= [x]
    ξ ::= v |-> EVar x

Theorem subst_remove_scope_rev : forall e Γ ξ l,
  (EXP Γ ++ l ⊢ subst ξ e -> forall vals, vals_subscoped vals Γ ->
     EXP Γ ⊢ subst (ξ[[ ::= combine l vals]]) e) /\
  (VAL Γ ++ l ⊢ subst ξ e -> forall vals, vals_subscoped vals Γ ->
     VAL Γ ⊢ subst (ξ[[ ::= combine l vals]]) e).
Proof.
  induction e; intros; split; intros.
  * constructor. constructor.
  * constructor.
  * constructor. simpl. simpl in H.
Admitted. *)

(* Fixpoint value_of_list (ξ : Substitution) (l : list VarFunId) : list Exp :=
match l with
| [] => []
| x::xs => ξ x :: value_of_list ξ xs
end.

Theorem restrict_add :
  forall l ξ, ξ = ((ξ -- l)[[::= combine l (value_of_list ξ l)]]).
Proof.
  (* unfold "--", extend_subst_list. *)
  induction l; intros.
  * simpl. reflexivity.
  * unfold "--", extend_subst_list. simpl. extensionality v.
    
Admitted.

Theorem alma : forall l Γ ξ,
  subscoped l Γ ξ ->
  vals_subscoped (value_of_list ξ l) Γ.
Proof.
Admitted. *)

(*
Does not hold, see previous counterexample:

Theorem subst_remove_scope_rev : forall e Γ Γ' ξ l,
  subscoped (Γ ++ l) Γ' ξ ->
  (EXP Γ ++ l ⊢ subst (ξ -- l) e -> EXP Γ' ⊢ subst ξ e) /\
  (VAL Γ ++ l ⊢ subst (ξ -- l) e -> VAL Γ' ⊢ subst ξ e).
Proof.
  
Admitted.
*)

Theorem idsubst_restrict_is_idsubst :
  forall l, idsubst -- l = idsubst.
Proof.
  intros. extensionality x. unfold "--". break_match_goal; auto.
Qed.

Hint Resolve idsubst_restrict_is_idsubst.

Theorem idsubst_is_id_helper el :
  Forall (fun e : Exp => subst idsubst e = e) el ->
  map (subst idsubst) el = el.
Proof.
  induction el; auto.
  simpl. intros. inversion H. subst. rewrite H2. rewrite IHel; auto. 
Qed.

Theorem idsubst_is_id :
  forall e, subst idsubst e = e.
Proof.
  induction e using Exp_ind2 with
    (Q := fun l => Forall (fun e => subst idsubst e = e) l); intros; simpl; auto.
  * rewrite idsubst_restrict_is_idsubst, IHe. auto.
  * rewrite idsubst_restrict_is_idsubst, IHe. auto.
  * rewrite IHe, idsubst_is_id_helper; auto.
  * rewrite idsubst_restrict_is_idsubst, IHe1, IHe2. auto.
  * repeat rewrite idsubst_restrict_is_idsubst. rewrite IHe1, IHe2. auto.
  * rewrite IHe1, IHe2. auto.
  * rewrite IHe1, IHe2, IHe3. auto.
Qed.

Theorem idsubst_scoped :
  forall Γ, subscoped Γ Γ idsubst.
Proof.
  intros. intro. intros. unfold idsubst. destruct v; constructor; auto.
Qed.

Hint Resolve idsubst_is_id.

Theorem subst_preserves_scope_exp : forall e Γ,
  (forall Γ' ξ,
      subscoped Γ Γ' ξ -> EXP Γ' ⊢ subst ξ e) -> EXP Γ ⊢ e.
Proof.
  intros. specialize (H Γ idsubst (idsubst_scoped _)).
  rewrite idsubst_is_id in H. auto.
Qed.

Theorem subst_preserves_scope_val : forall e Γ,
  (forall Γ' ξ,
      subscoped Γ Γ' ξ -> VAL Γ' ⊢ subst ξ e) -> VAL Γ ⊢ e.
Proof.
  intros. specialize (H Γ idsubst (idsubst_scoped _)).
  rewrite idsubst_is_id in H. auto.
Qed.


Theorem subst_preserves_scope_rev : forall e Γ,
  (EXP Γ ⊢ e ->
    forall Γ' ξ,
      subscoped Γ Γ' ξ -> EXP Γ' ⊢ subst ξ e) /\
  (VAL Γ ⊢ e ->
    forall Γ' ξ,
      subscoped Γ Γ' ξ -> VAL Γ' ⊢ subst ξ e).
Proof.
  induction e using Exp_ind2 with (Q := 
    fun l => Forall (fun e =>
      forall Γ, (EXP Γ ⊢ e ->
    forall Γ' ξ,
      subscoped Γ Γ' ξ -> EXP Γ' ⊢ subst ξ e) /\
  (VAL Γ ⊢ e ->
    forall Γ' ξ,
      subscoped Γ Γ' ξ -> VAL Γ' ⊢ subst ξ e)) l
  ); try split; intros.

(* LIT *)
  * unfold subst. constructor. constructor.
  * unfold subst. constructor.

(* VAR *)
  * inversion H. unfold subst. inversion H1. subst.
    unfold subscoped in H0. constructor. apply H0. auto.
  * inversion H. unfold subst. subst.
    unfold subscoped in H0. apply H0. auto.

(* FUNID *)
  * inversion H. unfold subst. inversion H1. subst.
    unfold subscoped in H0. constructor. apply H0. auto.
  * inversion H. unfold subst. subst.
    unfold subscoped in H0. apply H0. auto.

(* FUN *)
  * simpl. constructor. constructor. inversion H. inversion H1. subst.
    eapply IHe; eauto. 
  * simpl. constructor. inversion H. subst.
    eapply IHe; eauto.

 (* RECFUN *)
  * simpl. constructor. constructor. inversion H. inversion H1. subst.
    eapply IHe; eauto. 
  * simpl. constructor. inversion H. subst.
    eapply IHe; eauto.

(* APP *)
  * simpl. inversion H. 2: inversion H1. subst. constructor.
    - eapply IHe; eauto.
    - intros. rewrite indexed_to_forall in IHe0. rewrite map_length in H1.
      replace (ELit 0) with (subst ξ (ELit 0)) by reflexivity.
      rewrite map_nth. eapply IHe0; eauto.
  * inversion H.

(* LET *)
  * simpl. inversion H. subst. 2: inversion H1.
    constructor; [ eapply IHe1 | eapply IHe2 ]; eauto.
  * inversion H.

(* LETREC *)
  * simpl. inversion H. subst. 2: inversion H1.
    constructor; [ eapply IHe1 | eapply IHe2 ]; eauto.
  * inversion H.

(* PLUS *)
  * simpl. inversion H. subst. constructor; [ eapply IHe1 | eapply IHe2 ]; eauto.
    inversion H1.
  * inversion H.

(* IF *)
  * simpl. inversion H. subst. constructor; [ eapply IHe1 | eapply IHe2 | eapply IHe3 ]; eauto.
    inversion H1.
  * inversion H.

(* APP HELPERS *)
  * constructor. apply IHe. apply IHe0.
  * constructor.
Qed.






(** Subst implies scope *)

Definition partial_max (s1 s2 : Var) : string :=
  if String.length s1 <? String.length s2 then s2 else s1
.

(** Just append an 's' to the front *)
Definition string_succ (s : Var) : string := "s"%string ++ s.

(** Maximum element of a list, with the custom max *)
Definition list_max (l : list VarFunId) :=
  fold_right (fun x acc => match x with
                           | inl x' => partial_max x' acc
                           | _      => acc
                           end) EmptyString l.

Definition new_fresh (l : list VarFunId) : Var :=
  string_succ (list_max l).

Theorem succ_neq_s : forall s, s <> string_succ s.
Proof.
  intro. intro. unfold string_succ in H. simpl in H. 
  induction s; inversion H. subst. contradiction.
Qed.

Theorem max_not_in :
  forall l s, partial_max (list_max l) s = s -> ~In (inl s) l.
Proof.
  induction l; intros.
  * intro. inversion H0.
  * intro. destruct (var_funid_eqb (inl s) a) eqn:P.
    - apply var_funid_eqb_eq in P. subst.
      simpl in H. unfold partial_max in H. break_match_hyp.
      + break_match_hyp.
        ** subst. apply Nat.ltb_lt in Heqb. apply Nat.ltb_lt in Heqb0. lia.
        ** apply Nat.ltb_lt in Heqb. lia.
      + break_match_hyp. congruence. admit.
    - eapply IHl.
Admitted.

Theorem fresh_is_fresh :
  forall l, ~In (inl (new_fresh l)) l.
Proof.
  intros. unfold new_fresh.
  
  intros. induction l; auto.
  * simpl. intro.
Admitted.

Theorem app_in_not :
  forall {T : Type} (l1 l2 : list T) x, ~In x (l1 ++ l2) -> ~In x l1 /\ ~In x l2.
Proof.
  intros. firstorder; intro; assert (In x (l1 ++ l2)). 
  1, 3 : apply in_or_app; auto. all: congruence.
Qed.

(* Lemma magic_ξ_app_scope :
  forall e Γ Γ' fresh p1 p2 l,
  EXP Γ' ++ l ⊢ subst (magic_ξ Γ Γ' fresh p1 p2 -- l) e ->
  exists fresh p1 p2, EXP Γ' ⊢ subst (magic_ξ (Γ ++ l) Γ' fresh p1 p2) e.
Proof.
  induction e; intros.
  * exists (inl (new_fresh (Γ' ++ Γ ++ l0))).
    pose (fresh_is_fresh (Γ' ++ Γ ++ l0)). apply app_in_not in n. destruct n.
    exists H1, H0. simpl. constructor. constructor.
  * 
Admitted. *)

Corollary in_app_left {T : Type} :
  forall (l l' : list T) (x : T),
  In x l -> In x (l ++ l').
Proof.
  firstorder. apply in_app_iff. auto.
Qed.

Corollary in_app_right {T : Type} :
  forall (l l' : list T) (x : T),
  In x l -> In x (l' ++ l).
Proof.
  firstorder. apply in_app_iff. auto.
Qed.

Module magic_ξ_gen.

(* With fresh gen. *)
Definition magic_ξ (Γ Γ' : list VarFunId)
   : Substitution :=
  fun x =>
    if in_list x Γ then
      if in_list x Γ'
      then idsubst x
      else ELit 0
    else EVar (new_fresh (Γ ++ Γ')).

Lemma magic_ξ_scope :
  forall Γ Γ', subscoped Γ Γ' (magic_ξ Γ Γ').
Proof.
  intros. intro. intros. unfold magic_ξ. repeat break_match_goal.
  * apply in_list_sound in Heqb. apply in_list_sound in Heqb0.
    destruct v; constructor; auto.
  * constructor.
  * apply not_in_list_sound in Heqb. congruence.
Qed.

Lemma magic_ξ_app_scope :
  forall Γ Γ' l,
  magic_ξ Γ Γ' -- l = magic_ξ (Γ ++ l) (Γ' ++ l).
Proof.
  unfold "--", magic_ξ. intros.
  extensionality x. repeat break_match_goal; auto.
  * apply in_list_sound in Heqb. apply not_in_list_sound in Heqb1.
    apply app_in_not in Heqb1. intuition.
  * apply in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply app_in_not in Heqb0. intuition.
  * apply not_in_list_sound in Heqb3. apply in_list_sound in Heqb1.
    apply app_in_not in Heqb3. intuition.
  * apply in_list_sound in Heqb0. apply not_in_list_sound in Heqb2.
    apply app_in_not in Heqb2. intuition.
  * apply in_list_sound in Heqb3. apply not_in_list_sound in Heqb.
    apply not_in_list_sound in Heqb1.
    apply in_app_iff in Heqb3. intuition.
  * apply not_in_list_sound in Heqb2. apply app_in_not in Heqb2.
    apply in_list_sound in Heqb0. intuition.
  * apply not_in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply in_list_sound in Heqb1. apply in_app_iff in Heqb1. intuition.
  * apply not_in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply in_list_sound in Heqb1. apply in_app_iff in Heqb1. intuition.
  * admit.
Abort.

Theorem magic_extend_restrict :
  forall e Γ Γ' l,
  (EXP Γ' ++ l ⊢ subst (magic_ξ Γ Γ' -- l) e -> EXP Γ' ++ l ⊢ subst (magic_ξ (Γ ++ l) (Γ' ++ l)) e) /\
  (VAL Γ' ++ l ⊢ subst (magic_ξ Γ Γ' -- l) e -> VAL Γ' ++ l ⊢ subst (magic_ξ (Γ ++ l) (Γ' ++ l)) e).
Proof.
  induction e; intros; split; intros.
  1-2: constructor. constructor.
  * unfold magic_ξ, "--" in *. simpl in *. break_match_hyp.
    - apply in_list_sound in Heqb.
      eapply in_app_right with (l' := Γ) in Heqb as Heqb1.
      eapply in_app_right with (l' := Γ') in Heqb as Heqb2.
      apply in_list_sound in Heqb1. apply in_list_sound in Heqb2. rewrite Heqb1, Heqb2. auto.
    - break_match_hyp.
    2: {
Abort.

End magic_ξ_gen.

Definition magic_ξ (Γ Γ' : list VarFunId) (name : VarFunId)
   : Substitution :=
  fun x =>
    if in_list x Γ then
      if in_list x Γ'
      then idsubst x
      else ELit 0
    else idsubst name.

Lemma magic_ξ_scope :
  forall Γ Γ' name, subscoped Γ Γ' (magic_ξ Γ Γ' name).
Proof.
  intros. intro. intros. unfold magic_ξ. repeat break_match_goal.
  * apply in_list_sound in Heqb. apply in_list_sound in Heqb0.
    destruct v; constructor; auto.
  * constructor.
  * apply not_in_list_sound in Heqb. congruence.
Qed.

Theorem weaken_in {T : Type} : forall (l1 l2 l3 : list T) (x : T),
  ~ In x ((l1 ++ l2) ++ l3 ++ l2) -> ~In x (l1 ++ l3).
Proof.
  intros. intro.
  apply app_in_not in H. destruct H.
  apply app_in_not in H. apply app_in_not in H1. destruct H, H1.
  apply in_app_iff in H0. firstorder.
Qed.

Lemma magic_ξ_app_eq :
  forall Γ Γ' l name,
  magic_ξ Γ Γ' name -- l = magic_ξ (Γ ++ l) (Γ' ++ l) name.
Proof.
  unfold "--", magic_ξ. intros.
  extensionality x. repeat break_match_goal; auto.
  * apply in_list_sound in Heqb. apply not_in_list_sound in Heqb1.
    apply app_in_not in Heqb1. intuition.
  * apply in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply app_in_not in Heqb0. intuition.
  * apply not_in_list_sound in Heqb3. apply in_list_sound in Heqb1.
    apply app_in_not in Heqb3. intuition.
  * apply in_list_sound in Heqb0. apply not_in_list_sound in Heqb2.
    apply app_in_not in Heqb2. intuition.
  * apply in_list_sound in Heqb3. apply not_in_list_sound in Heqb.
    apply not_in_list_sound in Heqb1.
    apply in_app_iff in Heqb3. intuition.
  * apply not_in_list_sound in Heqb2. apply app_in_not in Heqb2.
    apply in_list_sound in Heqb0. intuition.
  * apply not_in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply in_list_sound in Heqb1. apply in_app_iff in Heqb1. intuition.
  * apply not_in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
    apply in_list_sound in Heqb1. apply in_app_iff in Heqb1. intuition.
Qed.

Fixpoint names (e : Exp) : list VarFunId :=
match e with
| ELit l => []
| EVar v => [inl v]
| EFunId f => [inr f]
| EFun vl e => map inl vl ++ names e
| ERecFun f vl e => (inr f :: map inl vl) ++ names e
| EApp exp l => names exp ++ flat_map names l
| ELet v e1 e2 => [inl v] ++ names e1 ++ names e2 
| ELetRec f vl b e => (inr f :: map inl vl) ++ names b ++ names e
| EPlus e1 e2 => names e1 ++ names e2
| EIf e1 e2 e3 => names e1 ++ names e2 ++ names e3
end.

Ltac app_in_not_tac :=
match goal with
| [ H : ~In _ (_ ++ _) |- _ ] => apply app_in_not in H
end.

Search In flat_map.

Lemma magic_ξ_name_irrelevant :
  forall e, 
  (forall Γ Γ' name, ~In name Γ -> ~In name Γ' -> ~In name (names e) ->
  EXP Γ' ⊢ subst (magic_ξ Γ Γ' name) e ->
  forall name', ~In name' Γ -> ~In name' Γ' -> ~In name' (names e) -> EXP Γ' ⊢ subst (magic_ξ Γ Γ' name') e) /\
  (forall Γ Γ' name, ~In name Γ -> ~In name Γ' -> ~In name (names e) ->
  VAL Γ' ⊢ subst (magic_ξ Γ Γ' name) e ->
  forall name', ~In name' Γ -> ~In name' Γ' -> ~In name' (names e) -> VAL Γ' ⊢ subst (magic_ξ Γ Γ' name') e).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => Forall (fun e => (forall Γ Γ' name, ~In name Γ -> ~In name Γ' -> ~In name (names e) ->
  EXP Γ' ⊢ subst (magic_ξ Γ Γ' name) e ->
  forall name', ~In name' Γ -> ~In name' Γ' -> ~In name' (names e) -> EXP Γ' ⊢ subst (magic_ξ Γ Γ' name') e) /\
  (forall Γ Γ' name, ~In name Γ -> ~In name Γ' -> ~In name (names e) ->
  VAL Γ' ⊢ subst (magic_ξ Γ Γ' name) e ->
  forall name', ~In name' Γ -> ~In name' Γ' -> ~In name' (names e) -> VAL Γ' ⊢ subst (magic_ξ Γ Γ' name') e)) l)
  ; try split; intros.
  1-2: constructor. constructor.

  (* VAR *)
  * simpl. unfold magic_ξ in *. simpl in *. break_match_goal. break_match_goal.
    - unfold idsubst. constructor. constructor. apply in_list_sound in Heqb0. auto.
    - constructor. constructor.
    - unfold idsubst in H2. destruct name; inversion H2; inversion H6; contradiction.
  * simpl. unfold magic_ξ in *. simpl in *. break_match_goal. break_match_goal.
    - unfold idsubst. constructor. apply in_list_sound in Heqb0. auto.
    - constructor.
    - unfold idsubst in H2. destruct name; inversion H2; inversion H6; subst; contradiction.

  (* FUNID *)
  * simpl. unfold magic_ξ in *. simpl in *. break_match_goal. break_match_goal.
    - unfold idsubst. constructor. constructor. apply in_list_sound in Heqb0. auto.
    - constructor. constructor.
    - unfold idsubst in H2. destruct name; inversion H2; inversion H6; subst; contradiction.
  * simpl. unfold magic_ξ in *. simpl in *. break_match_goal. break_match_goal.
    - unfold idsubst. constructor. apply in_list_sound in Heqb0. auto.
    - constructor.
    - unfold idsubst in H2. destruct name; inversion H2; inversion H6; subst; contradiction.

  (* FUN *)
  * simpl subst in *. inversion H2. inversion H6. subst.
    constructor. constructor. rewrite magic_ξ_app_eq in *.
    destruct IHe. simpl in H1. apply app_in_not in H1. destruct H1.
    simpl in H5. apply app_in_not in H5. destruct H5.
    eapply H7. 4: exact H9. all: auto. all: apply app_not_in; auto. 
  * simpl subst in *. inversion H2. subst.
    constructor. rewrite magic_ξ_app_eq in *.
    destruct IHe. simpl in H1. apply app_in_not in H1. destruct H1.
    simpl in H5. apply app_in_not in H5. destruct H5.
    eapply H6. 4: exact H7. all: auto. all: apply app_not_in; auto.

  (* RECFUN *)
  * simpl subst in *. inversion H2. inversion H6. subst.
    constructor. constructor. rewrite magic_ξ_app_eq in *.
    destruct IHe. apply app_in_not in H1. destruct H1.
    apply app_in_not in H5. destruct H5. fold names in *. (* Coq oversimplifies names *)
    eapply H7. 4: exact H9. all: auto. all: apply app_not_in; auto. 
  * simpl subst in *. inversion H2. subst.
    constructor. rewrite magic_ξ_app_eq in *.
    destruct IHe. apply app_in_not in H1. destruct H1.
    apply app_in_not in H5. destruct H5. fold names in *. (* Coq oversimplifies names *)
    eapply H6. 4: exact H7. all: auto. all: apply app_not_in; auto. 

  (* APP *)
  * simpl in H1, H5. repeat app_in_not_tac. destruct H1, H5.
    inversion H2. subst. simpl subst in *. constructor.
    - eapply IHe. 4: exact H10. all: auto.
    - intros. rewrite map_length in *. specialize (H11 i H8). rewrite indexed_to_forall in IHe0.
      specialize (IHe0 i H8). destruct IHe0.
      replace (ELit 0) with (subst (magic_ξ Γ Γ' name') (ELit 0)) by reflexivity.
      replace (ELit 0) with (subst (magic_ξ Γ Γ' name) (ELit 0)) in H11 by reflexivity.
      rewrite map_nth in *. eapply H9. 4: exact H11. all: auto.
      apply notin_flat_map_Forall in H6. rewrite indexed_to_forall in H6. apply H6. auto.
      apply notin_flat_map_Forall in H7. rewrite indexed_to_forall in H7. apply H7. auto.
    - inversion H8.
  * inversion H2.

  (* LET *)
  * simpl subst in *. inversion H2. subst. 
    apply app_in_not in H1. apply app_in_not in H5. fold names in *. destruct H1, H5.
    repeat app_in_not_tac. destruct H6, H7.
    constructor.
    - eapply IHe1. 4: exact H8. all: auto.
    - rewrite magic_ξ_app_eq in *. eapply IHe2. 4: exact H10. all: try apply app_not_in. all: auto.
    - inversion H6.
  * inversion H2.

  (* LETREC *)
  * simpl subst in *. inversion H2. subst.
    apply app_in_not in H1. apply app_in_not in H5. fold names in *. destruct H1, H5.
    repeat app_in_not_tac. destruct H6, H7.
    constructor.
    - rewrite magic_ξ_app_eq in *. eapply IHe1. 4: exact H8. all: try apply app_not_in. all: auto.
    - replace (inr f :: map inl vl) with ([inr f] ++ map inl vl) in * by reflexivity.
      repeat app_in_not_tac. destruct H1, H5.
      rewrite magic_ξ_app_eq in *. eapply IHe2. 4: exact H11. all: try apply app_not_in. all: auto.
    - inversion H6.
  * inversion H2.

  (* PLUS *)
  * simpl subst in *. inversion H2. subst. simpl in H5, H1. repeat app_in_not_tac. destruct H1, H5. 
    constructor.
    - eapply IHe1. 4: exact H8. all: eauto.
    - eapply IHe2. 4: exact H9. all: eauto.
    - inversion H6.
  * inversion H2.

  (* IF *)
  * simpl subst in *. inversion H2. subst. 
    simpl in H5, H1. repeat app_in_not_tac. destruct H1, H5.
    repeat app_in_not_tac. destruct H6, H7.
    constructor.
    - eapply IHe1. 4: exact H9. all: eauto.
    - eapply IHe2. 4: exact H10. all: eauto.
    - eapply IHe3. 4: exact H11. all: eauto.
    - inversion H6.
  * inversion H2.
  * constructor. eapply IHe. apply IHe0.
  * constructor.
Qed.

Lemma magic_ξ_implies_scope : forall e Γ Γ' name 
  (p1 : ~In name Γ) (p2 : ~In name Γ') (p3 : ~In name (names e)),
  (EXP Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> EXP Γ ⊢ e) /\
  (VAL Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> VAL Γ ⊢ e).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => list_forall (fun e => forall Γ Γ' name
  (p1 : ~In name Γ) (p2 : ~In name Γ') (p3 : ~In name (names e)),
    (EXP Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> EXP Γ ⊢ e) /\
    (VAL Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> VAL Γ ⊢ e)
  ) l); intros; try split; intros.
  * constructor. constructor.
  * constructor.
  * constructor. constructor. simpl in H. unfold magic_ξ in H. repeat break_match_hyp.
    - apply in_list_sound in Heqb. auto.
    - apply in_list_sound in Heqb. auto.
    - destruct name; inversion H; inversion H0; contradiction.
  * constructor. simpl in H. unfold magic_ξ in H. repeat break_match_hyp.
    - apply in_list_sound in Heqb. auto.
    - apply in_list_sound in Heqb. auto.
    - destruct name; inversion H; inversion H0; contradiction.
  * constructor. constructor. simpl in H. unfold magic_ξ in H. repeat break_match_hyp.
    - apply in_list_sound in Heqb. auto.
    - apply in_list_sound in Heqb. auto.
    - destruct name; inversion H; inversion H0; contradiction.
  * constructor. simpl in H. unfold magic_ξ in H. repeat break_match_hyp.
    - apply in_list_sound in Heqb. auto.
    - apply in_list_sound in Heqb. auto.
    - destruct name; inversion H; inversion H0; contradiction.
  * constructor. constructor. eapply magic_ξ_name_irrelevant in H; auto.
    simpl in H. inversion H. inversion H0. subst.
    erewrite magic_ξ_app_eq in H3. eapply (IHe _ (Γ' ++ map inl vl)). 4: exact H3. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. eapply magic_ξ_name_irrelevant in H; auto.
    simpl in H. inversion H. subst.
    erewrite magic_ξ_app_eq in H1. eapply (IHe _ (Γ' ++ map inl vl)). 4: exact H1. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. constructor. eapply magic_ξ_name_irrelevant in H; auto.
    simpl in H. inversion H. inversion H0. subst.
    erewrite magic_ξ_app_eq in H3. eapply (IHe _ (Γ' ++ inr f :: map inl vl)). 4: exact H3. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. eapply magic_ξ_name_irrelevant in H; auto.
    simpl in H. inversion H. subst.
    erewrite magic_ξ_app_eq in H1. eapply (IHe _ (Γ' ++ inr f :: map inl vl)). 4: exact H1. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * admit.
  * inversion H.
  * admit.
  * inversion H.
  * admit.
  * inversion H.
  * admit.
  * inversion H.
  * admit.
  * inversion H.
  * constructor. apply IHe. apply IHe0.
  * constructor.
Admitted.


Theorem sub_implies_scope :
  forall Γ e Γ',
  ((forall vals, length vals = length Γ -> 
     subscoped Γ' vals -> EXP Γ' ⊢ subst_list Γ vals e)
 -> EXP Γ ⊢ e) /\
  ((forall vals, length vals = length Γ -> 
     subscoped Γ' vals -> VAL Γ' ⊢ subst_list Γ vals e)
 -> VAL Γ ⊢ e).
Proof.
  induction Γ; intros; split; intros.
  * epose (H [] (eq_refl _) _). admit.
  * admit.
  * 
Admitted.

Goal EXP [] ⊢ EVar "X"%string.
Proof.
  eapply sub_implies_scope. intros.
  unfold subst_list. simpl. constructor. constructor.
  instantiate (1 := [inl "X"%string]). intuition.
Qed.

Goal ~ EXP [] ⊢ EVar "X"%string.
Proof.
  intro. inversion H. inversion H0. inversion H3.
Qed.

(* Corollary sub_implies_scope_exp : forall Γ e,
  (forall vals, length vals = length Γ -> subscoped [] vals
    -> EXPCLOSED (subst_list Γ vals e))
  ->
  EXP Γ ⊢ e.
Proof.
  intros.
  apply exp_subst_scope_rev. intros. simpl.
Admitted. *)




