Require Export SubstSemantics.
Export Relations.Relations.
Export Classes.RelationClasses.

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
| scoped_var v : In (inl v) l -> VAL l ⊢ EVar v
| scoped_funid f : In (inr f) l -> VAL l ⊢ EFunId f
| scoped_fun vl e : EXP (l ++ (map inl vl)) ⊢ e -> VAL l ⊢ EFun vl e
| scoped_recfun f vl e : EXP (l ++ [inr f] ++ (map inl vl)) ⊢ e -> VAL l ⊢ ERecFun f vl e
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
      (Q := fun l => list_forall (fun e => 
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

Theorem scope_sub v : forall e,
  (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
  (forall Γ, EXP (inl v::Γ) ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (varsubst v val e)).
Proof.
  einduction e using Exp_ind2 with 
  (Q := fun l => list_forall (fun e => (forall Γ, VAL (inl v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (varsubst v val e)) /\
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
  (Q := fun l => list_forall (fun e => (forall Γ, VAL (inr v::Γ) ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (funsubst v val e)) /\
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

Theorem scope_duplicate_rev e :
  (forall Γ v, In v Γ -> EXP Γ ⊢ e -> EXP v::Γ ⊢ e) /\
  (forall Γ v, In v Γ -> VAL Γ ⊢ e -> VAL v::Γ ⊢ e).
Proof.
  einduction e using Exp_ind2 with 
      (Q := fun l => list_forall (fun e => 
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
    - eapply IHe0_1. apply in_or_app. left. eauto. rewrite <- app_comm_cons in H3. auto.
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

Corollary scope_subst_in v : forall e,
  (forall Γ, In v Γ -> 
    VAL Γ ⊢ e -> forall val, VAL Γ ⊢ val -> VAL Γ ⊢ (subst v val e)) /\
  (forall Γ, In v Γ ->
    EXP Γ ⊢ e -> forall val, EXP Γ ⊢ val -> EXP Γ ⊢ (subst v val e)).
Proof.
  intros; split; intros.
  * apply scope_subst; auto. eapply scope_duplicate_rev in H; eauto.
  * apply scope_subst; auto. pose (scope_duplicate_rev e). destruct a. apply H2; eauto.
Qed.

Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Definition subscoped (l' : list VarFunId) (vals : list Exp) : Prop :=
  forall i, i < length vals -> ValScoped l' (nth i vals (ELit 0))
.

Corollary scope_subst_list Γ' : forall Γ e,
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
Qed.


Theorem subst_preserves_scope : forall e Γ v,
  (EXP v::Γ ⊢ e <->
    forall Γ' val,
      VAL Γ' ⊢ val -> EXP Γ' ++ Γ ⊢ subst v val e) /\
  (VAL v::Γ ⊢ e <->
    forall Γ' val,
      VAL Γ' ⊢ val -> VAL Γ' ++ Γ ⊢ subst v val e).
Proof.
(* MAJOR TODO: this proof could be shortened significantly *)
  induction e using Exp_ind2
  with (Q :=
    fun l => list_forall (
      fun e => forall Γ v, (EXP v::Γ ⊢ e <->
    forall Γ' val,
      VAL Γ' ⊢ val -> EXP Γ' ++ Γ ⊢ subst v val e) /\
  (VAL v::Γ ⊢ e <->
    forall Γ' val,
      VAL Γ' ⊢ val -> VAL Γ' ++ Γ ⊢ subst v val e)
    
    ) l
  ); try (split; intros; split; intros).

(* LIT *)
  * unfold subst. destruct v; simpl; constructor; constructor.
  * constructor. constructor.
  * unfold subst. destruct v; simpl; constructor.
  * constructor.

(* VAR *)
  * inversion H. unfold subst. break_match_goal; simpl. break_match_goal; simpl.
    - apply eqb_eq in Heqb. subst. apply scope_ext_app. constructor. auto.
    - apply eqb_neq in Heqb. subst. inversion H1. inversion H3. congruence.
      constructor. constructor. apply in_app_iff. right. auto.
    - inversion H1. inversion H4. congruence. constructor. constructor.
      apply in_app_iff. right. auto.
  * constructor. epose (H [] (ELit 0) _). simpl in e. unfold subst in e.
    break_match_hyp.
    - simpl in e. remember e as e'. clear Heqe' e. break_match_hyp.
      + apply eqb_eq in Heqb. constructor. subst. constructor. auto.
      + apply eqb_neq in Heqb. constructor. constructor 2. inversion e'. inversion H0.
        auto.
    - simpl in e. constructor. constructor 2. inversion e. inversion H0. auto.
  * inversion H. unfold subst. break_match_goal; simpl. break_match_goal; simpl.
    - apply eqb_eq in Heqb. subst. apply scope_ext_app. auto.
    - apply eqb_neq in Heqb. subst. inversion H2. congruence.
      constructor. apply in_app_iff. right. auto.
    - inversion H2. congruence. constructor. apply in_app_iff. right. auto.
  * epose (H [] (ELit 0) _ ). simpl in v1. unfold subst in v1.
    break_match_hyp.
    - simpl in v1. remember v1 as e'. clear Heqe' v1. break_match_hyp.
      + apply eqb_eq in Heqb. constructor. subst. constructor. auto.
      + apply eqb_neq in Heqb. constructor. constructor 2. inversion e'. inversion H0.
        auto.
    - simpl in v1. constructor. constructor 2. inversion v1. inversion H0. auto.

(* FUNID *)
  * inversion H. unfold subst. break_match_goal; simpl. 2: break_match_goal; simpl.
    - inversion H1. inversion H4. congruence. constructor. constructor.
      apply in_app_iff. right. auto.
    - apply funid_eqb_eq in Heqb. subst. apply scope_ext_app. constructor. auto.
    - apply funid_eqb_neq in Heqb. subst. inversion H1. inversion H3. congruence.
      constructor. constructor. apply in_app_iff. right. auto.
  * constructor. epose (H [] (ELit 0) _). simpl in e. unfold subst in e.
    break_match_hyp.
    - simpl in e. constructor. constructor 2. inversion e. inversion H0. auto.
    - simpl in e. remember e as e'. clear Heqe' e. break_match_hyp.
      + apply funid_eqb_eq in Heqb. constructor. subst. constructor. auto.
      + apply funid_eqb_neq in Heqb. constructor. constructor 2. inversion e'. inversion H0.
        auto.
  * inversion H. unfold subst. break_match_goal; simpl. 2: break_match_goal; simpl.
    - inversion H2. congruence. constructor. apply in_app_iff. right. auto.
    - apply funid_eqb_eq in Heqb. subst. apply scope_ext_app. auto.
    - apply funid_eqb_neq in Heqb. subst. inversion H2. congruence.
      constructor. apply in_app_iff. right. auto.
  * epose (H [] (ELit 0) _ ). simpl in v0. unfold subst in v0.
    break_match_hyp.
    - simpl in v0. constructor. constructor 2. inversion v0. inversion H0. auto.
    - simpl in v0. remember v0 as e'. clear Heqe' v0. break_match_hyp.
      + apply funid_eqb_eq in Heqb. constructor. subst. constructor. auto.
      + apply funid_eqb_neq in Heqb. constructor. constructor 2. inversion e'. inversion H0.
        auto.

(* FUN *)
  * unfold subst. inversion H. inversion H1. subst. break_match_goal.
    - simpl. break_match_goal.
      + apply in_list_sound in Heqb. constructor. constructor.
        rewrite <- app_comm_cons in H4. apply scope_duplicate in H4.
        rewrite <- app_assoc. eapply scope_ext_app in H4. rewrite <- app_assoc in H4.
        pose (perm_scoped (Γ' ++ Γ ++ map inl vl)). destruct a. clear H2.
        eapply perm_scoped in H4. specialize (H3 e H4). auto.
        instantiate (1 := Γ'). Search Permutation app.
        pose (Permutation_app_rot Γ' Γ (map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_map. auto.
      + constructor. constructor. rewrite <- app_assoc. eapply (IHe _ (inl v0)); auto.
    - simpl. constructor. constructor. rewrite <- app_assoc.
      eapply (IHe _ (inr f)); auto.
  * constructor. constructor. rewrite <- app_comm_cons.
    epose (H [] (ELit 0) _). 
    unfold subst in e0. break_match_hyp. simpl in e0.
    remember e0 as e0'. clear Heqe0' e0. break_match_hyp.
    - inversion e0'. inversion H0. subst. apply scope_ext. auto.
    - inversion e0'. inversion H0. subst. eapply IHe. intros.
      epose (H Γ' val _). unfold subst in *.
      simpl in e0. rewrite Heqb in e0. inversion e0. inversion H2. subst.
      rewrite app_assoc. auto.
    - subst. eapply IHe. intros. epose (H Γ' val _). inversion e1.
      inversion H1. subst. rewrite app_assoc. auto.
  * unfold subst. inversion H. inversion H1. subst. break_match_goal.
    - simpl. break_match_goal.
      + apply in_list_sound in Heqb. constructor. subst.
        rewrite <- app_comm_cons in H2. apply scope_duplicate in H2.
        rewrite <- app_assoc. eapply scope_ext_app in H2. rewrite <- app_assoc in H2.
        pose (perm_scoped (Γ' ++ Γ ++ map inl vl)). destruct a. clear H1.
        eapply perm_scoped in H2. specialize (H3 e H2). auto.
        instantiate (1 := Γ'). Search Permutation app.
        pose (Permutation_app_rot Γ' Γ (map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_map. auto.
      + constructor. rewrite <- app_assoc. eapply (IHe _ (inl v0)); auto.
    - simpl. constructor. rewrite <- app_assoc.
      eapply (IHe _ (inr f)); auto.
  * constructor. rewrite <- app_comm_cons.
    epose (H [] (ELit 0) _).
    unfold subst in v0. break_match_hyp. simpl in v0.
    remember v0 as e0'. clear Heqe0' v0. break_match_hyp.
    - inversion e0'. inversion H0. subst. apply scope_ext. auto.
    - inversion e0'. inversion H0. subst. eapply IHe. intros.
      epose (H Γ' val _). unfold subst in *.
      simpl in v. rewrite Heqb in v. inversion v. inversion H2. subst.
      rewrite app_assoc. auto.
    - subst. eapply IHe. intros. epose (H Γ' val _). inversion v.
      inversion H1. subst. rewrite app_assoc. auto.

 (* RECFUN *)
  * unfold subst. inversion H. inversion H1. subst. break_match_goal.
    - simpl. break_match_goal.
      + apply in_list_sound in Heqb. constructor. constructor.
        rewrite <- app_comm_cons in H4. apply scope_duplicate in H4.
        rewrite <- app_assoc. eapply scope_ext_app in H4. rewrite <- app_assoc in H4.
        pose (perm_scoped (Γ' ++ Γ ++ [inr f] ++ map inl vl)). destruct a. clear H2.
        eapply perm_scoped in H4. specialize (H3 e H4). auto.
        instantiate (1 := Γ'). Search Permutation app.
        pose (Permutation_app_rot Γ' Γ ([inr f] ++ map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_app_iff. right. apply in_map. auto.
      + constructor. constructor. rewrite <- app_assoc. eapply (IHe _ (inl v0)); auto.
    - simpl. constructor. break_match_goal; constructor; rewrite <- app_assoc.
      + apply funid_eqb_eq in Heqb. subst.
        rewrite <- app_comm_cons in H4. apply scope_duplicate in H4.
        eapply scope_ext_app in H4.
        eapply perm_scoped. exact H4. rewrite <- app_assoc.
        instantiate (1 := Γ').
        pose (Permutation_app_rot Γ' Γ ([inr f0] ++ map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
      + eapply (IHe (Γ ++ [inr f] ++ map inl vl) (inr f0)); auto.
  * constructor. constructor. rewrite <- app_comm_cons.
    epose (H [] (ELit 0) _). 
    unfold subst in e0. break_match_hyp. simpl in e0.
    remember e0 as e0'. clear Heqe0' e0. break_match_hyp.
    - inversion e0'. inversion H0. subst. apply scope_ext. auto.
    - inversion e0'. inversion H0. subst. eapply IHe. intros.
      epose (H Γ' val _). unfold subst in *.
      simpl in e0. rewrite Heqb in e0. inversion e0. inversion H2. subst.
      rewrite app_assoc. auto.
    - subst. intros. epose (H [] (ELit 0) _). unfold subst in e1.
      simpl in e1. remember e1 as e1'. clear Heqe1' e1.
      break_match_hyp; inversion e1'; inversion H0; subst.
      + apply funid_eqb_eq in Heqb. subst. apply scope_duplicate_rev.
        apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
        auto.
      + apply IHe. intros. epose (H Γ' val _). unfold subst in *.
        simpl in e1. rewrite Heqb in e1. inversion e1. inversion H2. subst.
        rewrite app_assoc. auto.
  * unfold subst. inversion H. inversion H1. subst. break_match_goal.
    - simpl. break_match_goal.
      + apply in_list_sound in Heqb. constructor.
        rewrite <- app_comm_cons in H2. apply scope_duplicate in H2.
        rewrite <- app_assoc. eapply scope_ext_app in H2. rewrite <- app_assoc in H2.
        pose (perm_scoped (Γ' ++ Γ ++ [inr f] ++ map inl vl)). destruct a. clear H1.
        eapply perm_scoped in H2. specialize (H3 e H2). auto.
        instantiate (1 := Γ'). Search Permutation app.
        pose (Permutation_app_rot Γ' Γ ([inr f] ++ map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_app_iff. right. apply in_map. auto.
      + constructor. rewrite <- app_assoc. eapply (IHe _ (inl v0)); auto.
    - simpl. break_match_goal; constructor; rewrite <- app_assoc.
      + apply funid_eqb_eq in Heqb. subst.
        rewrite <- app_comm_cons in H2. apply scope_duplicate in H2.
        eapply scope_ext_app in H2.
        eapply perm_scoped. exact H2. rewrite <- app_assoc.
        instantiate (1 := Γ').
        pose (Permutation_app_rot Γ' Γ ([inr f0] ++ map inl vl)). apply Permutation_sym in p. auto.
        apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
      + eapply (IHe (Γ ++ [inr f] ++ map inl vl) (inr f0)); auto.
  * constructor. rewrite <- app_comm_cons.
    epose (H [] (ELit 0) _). 
    unfold subst in v0. break_match_hyp. simpl in v0.
    remember v0 as e0'. clear Heqe0' v0. break_match_hyp.
    - inversion e0'. inversion H0. subst. apply scope_ext. auto.
    - inversion e0'. inversion H0. subst. eapply IHe. intros.
      epose (H Γ' val _). unfold subst in *.
      simpl in v. rewrite Heqb in v. inversion v. inversion H2. subst.
      rewrite app_assoc. auto.
    - subst. intros. epose (H [] (ELit 0) _). unfold subst in v.
      simpl in v. remember v as e1'. clear Heqe1' v.
      break_match_hyp; inversion e1'; inversion H0; subst.
      + apply funid_eqb_eq in Heqb. subst. apply scope_duplicate_rev.
        apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
        auto.
      + apply IHe. intros. epose (H Γ' val _). unfold subst in *.
        simpl in v. rewrite Heqb in v. inversion v. inversion H2. subst.
        rewrite app_assoc. auto.

(* APP *)
  * unfold subst. destruct v.
    - simpl. inversion H. 2: inversion H1. constructor.
      + apply (IHe _ (inl v)). auto. auto.
      + rewrite indexed_to_forall in IHe0. intros.
        replace (ELit 0) with (varsubst v val (ELit 0)) by reflexivity.
        rewrite map_nth. eapply (IHe0 i _ _ (inl v)). apply H4.
        rewrite map_length in H5. auto. auto.
    - simpl. inversion H. 2: inversion H1. constructor.
      + apply (IHe _ (inr f)). auto. auto.
      + rewrite indexed_to_forall in IHe0. intros.
        replace (ELit 0) with (funsubst f val (ELit 0)) by reflexivity.
        rewrite map_nth. eapply (IHe0 i _ _ (inr f)). apply H4.
        rewrite map_length in H5. auto. auto.
  * destruct v.
    - constructor.
      + apply IHe. intros. epose (H _ val H0). unfold subst in e0. simpl in e0.
        inversion e0. 2: inversion H1. subst. auto.
      + rewrite indexed_to_forall in IHe0. intros. apply IHe0. auto. intros.
        epose (H _ val H1). unfold subst in e0. simpl in e0.
        inversion e0. 2: inversion H2. subst. unfold subst.
        rewrite <- map_nth. simpl. apply H5. rewrite map_length. auto.
    - constructor. (* duplicate *)
      + apply IHe. intros. epose (H _ val H0). unfold subst in e0. simpl in e0.
        inversion e0. 2: inversion H1. subst. auto.
      + rewrite indexed_to_forall in IHe0. intros. apply IHe0. auto. intros.
        epose (H _ val H1). unfold subst in e0. simpl in e0.
        inversion e0. 2: inversion H2. subst. unfold subst.
        rewrite <- map_nth. simpl. apply H5. rewrite map_length. auto.
  * inversion H.
  * epose (H [] (ELit 0) _). unfold subst in v0. break_match_hyp; inversion v0.

(* LET *)
  * inversion H. 2: inversion H1. subst. unfold subst. break_match_goal; simpl.
    break_match_goal.
    - apply eqb_eq in Heqb. subst. constructor.
      apply (IHe1 _ (inl v1)); eauto.
      rewrite <- app_comm_cons in H5. apply scope_duplicate in H5.
      eapply scope_ext_app in H5.
      eapply perm_scoped. exact H5. instantiate (1 := Γ').
      repeat rewrite <- app_assoc. pose (Permutation_app_rot Γ' Γ [inl v1]). apply Permutation_sym in p. auto. apply in_app_iff. right. constructor. auto.
    - constructor.
      eapply (IHe1 _ (inl v1)); eauto.
      rewrite <- app_assoc. eapply (IHe2 _ (inl v1)); eauto.
    - constructor.
      eapply (IHe1 _ (inr f)); eauto.
      rewrite <- app_assoc. eapply (IHe2 _ (inr f)); eauto.
  * destruct (var_funid_eqb v0 (inl v)) eqn:P.
    - apply var_funid_eqb_eq in P. subst. constructor.
      apply IHe1. intros. unfold subst. epose (H Γ' val H0).
      unfold subst in e. simpl in e. rewrite eqb_refl in e. 
      inversion e. 2: inversion H1. subst. auto.
      epose (H [] (ELit 0) _). unfold subst in e. simpl in e.
      rewrite eqb_refl in e. inversion e. 2: inversion H0. subst.
      eapply scope_duplicate_rev in H4. rewrite <- app_comm_cons. eauto.
      apply in_app_iff. right. intuition.
    - unfold subst in H. apply var_funid_eqb_neq in P. break_match_hyp.
      constructor.
      + apply IHe1. intros. epose (H Γ' val H0). simpl in e.
        remember e as e'. clear Heqe' e.
        break_match_hyp. apply eqb_eq in Heqb. subst. contradiction.
        inversion e'. auto. inversion H1.
      + apply IHe2. intros. epose (H Γ' val H0). simpl in e.
        remember e as e'. clear Heqe' e.
        break_match_hyp. apply eqb_eq in Heqb. subst. contradiction.
        inversion e'. 2: inversion H1. subst. rewrite app_assoc. exact H5.
      + constructor.
        apply IHe1. intros. epose (H Γ' val H0). simpl in e.
        inversion e. auto. inversion H1.
        apply IHe2. intros. epose (H Γ' val H0). simpl in e.
        inversion e. subst. rewrite app_assoc. auto. inversion H1.
  * inversion H.
  * epose (H [] (ELit 0) _). unfold subst in v1. break_match_hyp.
    simpl in v1. remember v1 as v1'. clear Heqv1' v1.
    break_match_hyp; inversion v1'. inversion v1. 

(* LETREC *)
  * inversion H. subst. 2: inversion H1.
    unfold subst. break_match_goal.
    - simpl. break_match_goal.
      + apply in_list_sound in Heqb. constructor.
        ** rewrite <- app_assoc. rewrite <- app_comm_cons in H3.
           apply scope_duplicate in H3. eapply scope_ext_app with (l := Γ') in H3.
           eapply perm_scoped in H3. exact H3. apply Permutation_app_comm.
           apply in_app_iff. right. apply in_app_iff. right. apply in_map. auto.
        ** rewrite <- app_assoc. apply (IHe2 _ (inl v0)). auto. auto.
      + constructor.
        ** rewrite <- app_assoc. apply (IHe1 _ (inl v0)). auto. auto.
        ** rewrite <- app_assoc. apply (IHe2 _ (inl v0)). auto. auto.
    - simpl. break_match_goal.
      + apply funid_eqb_eq in Heqb. subst. constructor.
        ** rewrite <- app_assoc. rewrite <- app_comm_cons in H3.
           apply scope_duplicate in H3. apply scope_ext_app with (l := Γ') in H3.
           eapply perm_scoped in H3. exact H3. apply Permutation_app_comm.
           apply in_app_iff. right. apply in_app_iff. left. constructor. auto.
        ** rewrite <- app_assoc. rewrite <- app_comm_cons in H6.
           apply scope_duplicate in H6. apply scope_ext_app with (l := Γ') in H6.
           eapply perm_scoped in H6. exact H6. apply Permutation_app_comm.
           apply in_app_iff. right. constructor. auto.
     + constructor.
       ** rewrite <- app_assoc. apply (IHe1 _ (inr f0)). auto. auto.
       ** rewrite <- app_assoc. apply (IHe2 _ (inr f0)). auto. auto.
  * destruct v.
    (* v was variable *)
    - destruct (in_list v vl) eqn:P.
      + simpl in H. rewrite P in H. constructor.
        ** rewrite <- app_comm_cons. apply scope_duplicate_rev.
           apply in_app_iff. right. apply in_app_iff. right. apply in_map.
           apply in_list_sound. auto.
           specialize (H [] (ELit 0) (scoped_lit _ _)). inversion H. 2: inversion H0.
           subst. simpl in H2. auto.
        ** rewrite <- app_comm_cons. apply IHe2. intros.
           specialize (H Γ' val H0). inversion H. 2: inversion H1. subst.
           rewrite <- app_assoc in H6. auto.
      + constructor.
        ** rewrite <- app_comm_cons. apply IHe1. intros.
           specialize (H Γ' val H0). unfold subst in H. simpl in H. rewrite P in H.
           inversion H. 2: inversion H1. subst.
           rewrite <- app_assoc in H3. auto.
        ** rewrite <- app_comm_cons. apply IHe2. intros.
           specialize (H Γ' val H0). unfold subst in H. simpl in H. rewrite P in H.
           inversion H. 2: inversion H1. subst.
           rewrite <- app_assoc in H6. auto.
    (* v was funid *)
    - destruct (funid_eqb f f0) eqn:P.
      + specialize (H [] (ELit 0) (scoped_lit _ _)).
        unfold subst in H. simpl in H. rewrite P in H. inversion H; subst.
        2: inversion H0. constructor.
        ** apply funid_eqb_eq in P. subst.
           rewrite <- app_comm_cons. apply scope_duplicate_rev.
           apply in_app_iff. right. apply in_app_iff. left. constructor. auto. auto.
        ** apply funid_eqb_eq in P. subst.
           rewrite <- app_comm_cons. apply scope_duplicate_rev.
           apply in_app_iff. right. constructor. auto. auto.
      + constructor. (* this is duplicate from before *)
        ** rewrite <- app_comm_cons. apply IHe1. intros.
           specialize (H Γ' val H0). unfold subst in H. simpl in H. rewrite P in H.
           inversion H. 2: inversion H1. subst.
           rewrite <- app_assoc in H3. auto.
        ** rewrite <- app_comm_cons. apply IHe2. intros.
           specialize (H Γ' val H0). unfold subst in H. simpl in H. rewrite P in H.
           inversion H. 2: inversion H1. subst.
           rewrite <- app_assoc in H6. auto.
  * inversion H.
  * epose (H [] (ELit 0) _). unfold subst in v0. break_match_hyp.
    simpl in v0. remember v0 as v1'. clear Heqv1' v0. break_match_hyp; inversion v1'. simpl in v0.
    remember v0 as v1'. clear Heqv1' v0. break_match_hyp; inversion v1'.

(* PLUS *)
  * inversion H. 2: inversion H1.
    unfold subst. break_match_goal; simpl; constructor.
    - eapply (IHe1 _ (inl v0)); eauto.
    - eapply (IHe2 _ (inl v0)); eauto.
    - eapply (IHe1 _ (inr f)); eauto.
    - eapply (IHe2 _ (inr f)); eauto.
  * constructor.
    - apply IHe1. intros. epose (H Γ' val _). unfold subst in e.
      break_match_hyp.
      all : unfold subst; inversion e; auto; inversion H1.
    - apply IHe2. intros. epose (H Γ' val _). unfold subst in e.
      break_match_hyp.
      all : unfold subst; inversion e; auto; inversion H1.
  * inversion H.
  * epose (H [] (ELit 0) _). unfold subst in v0. break_match_hyp; inversion v0.

(* IF *)
  * inversion H. 2: inversion H1.
    unfold subst. break_match_goal; simpl; constructor.
    - eapply (IHe1 _ (inl v0)); eauto.
    - eapply (IHe2 _ (inl v0)); eauto.
    - eapply (IHe3 _ (inl v0)); eauto.
    - eapply (IHe1 _ (inr f)); eauto.
    - eapply (IHe2 _ (inr f)); eauto.
    - eapply (IHe3 _ (inr f)); eauto.
  * constructor.
    - apply IHe1. intros. epose (H Γ' val _). unfold subst in e.
      break_match_hyp.
      all : unfold subst; inversion e; auto; inversion H1.
    - apply IHe2. intros. epose (H Γ' val _). unfold subst in e.
      break_match_hyp.
      all : unfold subst; inversion e; auto; inversion H1.
    - apply IHe3. intros. epose (H Γ' val _). unfold subst in e.
      break_match_hyp.
      all : unfold subst; inversion e; auto; inversion H1.
  * inversion H.
  * epose (H [] (ELit 0) _). unfold subst in v0. break_match_hyp; inversion v0.
  * constructor.
    - intros. apply IHe.
    - apply IHe0.
  * constructor.
Unshelve. all: try constructor; auto.
          all: rewrite map_length in H5; auto.
Qed.


Theorem closed_subst_to_scope : forall e, (forall Γ a v,
  VAL Γ ⊢ subst a v e -> VALCLOSED v -> VAL a :: Γ ⊢ e)
  /\
  (forall Γ a v, EXP Γ ⊢ subst a v e -> VALCLOSED v -> EXP a :: Γ ⊢ e).
Proof.
  induction e using Exp_ind2
  with (Q := fun l => list_forall (fun e => ( forall Γ a v,
  VAL Γ ⊢ subst a v e -> VALCLOSED v -> VAL a :: Γ ⊢ e)
  /\
  (forall Γ a v, EXP Γ ⊢ subst a v e -> VALCLOSED v -> EXP a :: Γ ⊢ e)) l); try split; intros.
  * constructor.
  * repeat constructor.
  * constructor. unfold subst in H. destruct a.
    + simpl in H. break_match_hyp. apply eqb_eq in Heqb. subst.
      constructor. auto. constructor 2. inversion H. auto.
    + constructor 2. inversion H. auto.
  * constructor. unfold subst in H. destruct a.
    + simpl in H. break_match_hyp. apply eqb_eq in Heqb. subst.
      constructor. constructor. auto. constructor. constructor 2. inversion H. inversion H1. auto.
    + constructor. constructor 2. inversion H. inversion H1. auto.
  * constructor. unfold subst in H. destruct a.
    + constructor 2. inversion H. auto.
    + simpl in H. break_match_hyp. apply funid_eqb_eq in Heqb. subst.
      constructor. auto. constructor 2. inversion H. auto.
  * constructor. unfold subst in H. destruct a.
    + constructor. constructor 2. inversion H. inversion H1. auto.
    + simpl in H. break_match_hyp. apply funid_eqb_eq in Heqb. subst.
      constructor. constructor. auto. constructor. constructor 2. inversion H. inversion H1. auto.
  * constructor. unfold subst in H. break_match_hyp. simpl in H. break_match_hyp.
    + apply in_list_sound in Heqb. subst. inversion H. subst.
      rewrite <- app_comm_cons. eapply scope_duplicate_rev.
      apply in_app_iff. right. apply in_map. auto. auto.
    + apply not_in_list_sound in Heqb. subst.
      inversion H. subst. rewrite <- app_comm_cons. eapply IHe; eauto.
    + subst. simpl in H. inversion H. subst. rewrite <- app_comm_cons. eapply IHe; eauto.
  * constructor. unfold subst in H. break_match_hyp. simpl in H. break_match_hyp.
    + apply in_list_sound in Heqb. subst. inversion H. inversion H1. subst.
      constructor. rewrite <- app_comm_cons. eapply scope_duplicate_rev.
      apply in_app_iff. right. apply in_map. auto. auto.
    + apply not_in_list_sound in Heqb. subst.
      inversion H. inversion H1. subst. constructor.
      rewrite <- app_comm_cons. eapply IHe; eauto.
    + subst. simpl in H. inversion H. inversion H1. subst. constructor. rewrite <- app_comm_cons. eapply IHe; eauto.
  * constructor. unfold subst in H. break_match_hyp. simpl in H. break_match_hyp.
    + apply in_list_sound in Heqb. subst. inversion H. subst.
      rewrite <- app_comm_cons. eapply scope_duplicate_rev.
      apply in_app_iff. right. apply in_app_iff. right. apply in_map. auto. auto.
    + apply not_in_list_sound in Heqb. subst.
      inversion H. subst. rewrite <- app_comm_cons. eapply IHe; eauto.
    + subst. simpl in H. break_match_hyp.
      ** inversion H. subst. rewrite <- app_comm_cons. apply scope_duplicate_rev.
         apply in_app_iff. right. apply in_app_iff. left. constructor.
         apply funid_eqb_eq in Heqb. subst. auto. auto.
      ** subst. simpl in H. inversion H. inversion H1. subst. rewrite <- app_comm_cons. eapply IHe; eauto. 
  * constructor. unfold subst in H. break_match_hyp. simpl in H. break_match_hyp.
    + apply in_list_sound in Heqb. subst. inversion H. inversion H1. subst.
      constructor. rewrite <- app_comm_cons. eapply scope_duplicate_rev.
      apply in_app_iff. right. apply in_app_iff. right. apply in_map. auto. auto.
    + apply not_in_list_sound in Heqb. subst.
      inversion H. inversion H1. subst. constructor.
      rewrite <- app_comm_cons. eapply IHe; eauto.
    + subst. simpl in H. break_match_hyp.
      ** inversion H. inversion H1.
         subst. constructor. rewrite <- app_comm_cons. apply scope_duplicate_rev.
         apply in_app_iff. right. apply in_app_iff. left. constructor.
         apply funid_eqb_eq in Heqb. subst. auto. auto.
      ** subst. simpl in H. inversion H. inversion H1. subst.
         constructor. rewrite <- app_comm_cons. eapply IHe; eauto.
  * unfold subst in H. break_match_hyp; inversion H.
  * unfold subst in H. break_match_hyp; simpl in H; constructor.
    - eapply IHe; eauto. inversion H. 2: inversion H1. exact H3.
    - intros. rewrite indexed_to_forall in IHe0. eapply IHe0; try lia; eauto.
      inversion H. 2: inversion H2. rewrite map_length in H5.
      specialize (H5 i H1). unfold subst. erewrite <- map_nth. simpl. auto.
    - eapply IHe; eauto. inversion H. 2: inversion H1. exact H3.
    - intros. rewrite indexed_to_forall in IHe0. eapply IHe0; try lia; eauto.
      inversion H. 2: inversion H2. rewrite map_length in H5.
      specialize (H5 i H1). unfold subst. erewrite <- map_nth. simpl. auto.
  * unfold subst in H. break_match_hyp. simpl in H. break_match_hyp; inversion H.
    simpl in H. inversion H.
  * unfold subst in H. break_match_hyp; simpl in H. break_match_hyp.
    - inversion H. 2: inversion H1. subst. constructor.
      apply eqb_eq in Heqb. subst. eapply IHe1; eauto.
      apply eqb_eq in Heqb. subst. rewrite <- app_comm_cons.
      apply scope_duplicate_rev. apply in_app_iff. right. constructor. auto. auto.
    - inversion H. 2: inversion H1. subst. constructor.
      apply eqb_neq in Heqb. eapply IHe1; eauto.
      eapply IHe2; eauto.
    - inversion H. 2: inversion H1. subst. constructor.
      eapply IHe1; eauto.
      eapply IHe2; eauto.
  * unfold subst in H. break_match_hyp. simpl in H. break_match_hyp; inversion H.
    simpl in H. break_match_hyp; inversion H.
  * unfold subst in H. break_match_hyp; simpl in H. break_match_hyp.
    - inversion H. 2: inversion H1.
      subst. apply in_list_sound in Heqb. subst. constructor.
      rewrite <- app_comm_cons; apply scope_duplicate_rev.
      apply in_app_iff; right. apply in_app_iff. right. apply in_map. auto. auto.
      eapply IHe2; eauto.
    - inversion H. 2: inversion H1. constructor.
      eapply IHe1; eauto. eapply IHe2; eauto.
    - break_match_hyp.
      + apply funid_eqb_eq in Heqb. inversion H. 2: inversion H1. subst.
        constructor. all: rewrite <- app_comm_cons; apply scope_duplicate_rev; 
          auto; apply in_app_iff; right.
        apply in_app_iff. left. all: constructor; auto.
      + inversion H. 2: inversion H1. subst. constructor.
        eapply IHe1; eauto. eapply IHe2; eauto.
  * unfold subst in H. break_match_hyp; inversion H.
  * unfold subst in H. break_match_hyp;
    inversion H. 2, 4: inversion H1. all: constructor.
    1, 3: eapply IHe1; eauto. all: eapply IHe2; eauto.
  * unfold subst in H. break_match_hyp; inversion H.
  * unfold subst in H. break_match_hyp;
    inversion H. 2, 4: inversion H1. all: constructor; subst.
    1, 4: eapply IHe1; eauto.
    1, 3: eapply IHe2; eauto.
    all: eapply IHe3; eauto.
  * inversion IHe0; subst. constructor; auto.
    constructor. auto. constructor. auto. auto.
  * constructor.
Qed.


Corollary subst_list_preserves_scope : forall Γ,
  (forall e, EXP Γ ⊢ e <->
    forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> EXP Γ' ⊢ subst_list Γ vals e) /\
  (forall e, VAL Γ ⊢ e <->
    forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> VAL Γ' ⊢ subst_list Γ vals e).
Proof.
  induction Γ.
  * unfold subst_list. simpl. split; split; intros.
    - replace Γ' with ([] ++ Γ') by auto. apply scope_ext_app. auto.
    - eapply H with (vals := []). auto. intro. intros. inversion H0.
    - replace Γ' with ([] ++ Γ') by auto. apply scope_ext_app. auto.
    - eapply H with (vals := []). auto. intro. intros. inversion H0.
  * split; split; intros.
    1, 3: simpl in H0; eapply eq_sym, element_exist in H0 as EE; destruct EE, H2; subst; unfold subst_list; simpl;
      replace (fold_left (fun (acc : Exp) '(v, val) => subst v val acc) (combine Γ x0) (subst a x e)) with (subst_list Γ x0 (subst a x e)) by auto.
    - 
      eapply scope_subst_list. eapply subst_preserves_scope. auto. eapply (H1 0 _).
      inversion H0. auto. intro. intros. eapply (H1 (S i) _). 
    - eapply scope_subst_list. eapply subst_preserves_scope. auto. eapply (H1 0 _).
      inversion H0. auto. intro. intros. eapply (H1 (S i) _). 
    - destruct IHΓ. clear H1.
      eapply closed_subst_to_scope. instantiate (1 := ELit 0). 2: constructor.
      apply H0. intros. epose (H Γ' ((ELit 0)::vals) _ _).
      exact e0.
    - destruct IHΓ. clear H0.
      eapply closed_subst_to_scope. instantiate (1 := ELit 0). 2: constructor.
      apply H1. intros. epose (H Γ' ((ELit 0)::vals) _ _).
      exact v.
Unshelve.
  all: simpl; try lia.
  all: intro; intros; destruct i.
  1, 3: simpl; replace Γ' with ([] ++ Γ') by auto; apply scope_ext_app; constructor.
  all: apply H2; simpl in H3; lia.
Qed.

Corollary exp_subst_scope : forall Γ,
  (forall e, EXP Γ ⊢ e ->
    forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> EXP Γ' ⊢ subst_list Γ vals e).
Proof.
  apply subst_list_preserves_scope.
Qed.

Corollary val_subst_scope : forall Γ,
  (forall e, VAL Γ ⊢ e ->
    forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> VAL Γ' ⊢ subst_list Γ vals e).
Proof.
  apply subst_list_preserves_scope.
Qed.

Corollary exp_subst_scope_rev : forall Γ,
  (forall e, 
    (forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> EXP Γ' ⊢ subst_list Γ vals e) -> EXP Γ ⊢ e).
Proof.
  apply subst_list_preserves_scope.
Qed.

Corollary val_subst_scope_rev : forall Γ,
  (forall e, 
    (forall Γ' vals, length vals = length Γ ->
      subscoped Γ' vals -> VAL Γ' ⊢ subst_list Γ vals e) -> VAL Γ ⊢ e).
Proof.
  apply subst_list_preserves_scope.
Qed.

(* Lemma sub_implies_scope_exp_single e : forall Γ x,
  (forall val, VAL Γ ⊢ val ->
    EXP Γ ⊢ (subst x val e))
  ->
  EXP (x::Γ) ⊢ e.
Proof.
  induction e; intros; constructor.
  * constructor.
  * epose (H (ELit 0) _). destruct (var_funid_eqb (inl v) x) eqn:P.
    - apply var_funid_eqb_eq in P. subst. simpl. left. auto.
    - constructor 2. unfold subst in e. apply var_funid_eqb_neq in P.
      destruct x.
      + simpl in e. destruct (string_dec v v0). subst. contradiction.
        apply eqb_neq in n. rewrite n in e. inversion e; auto. inversion H0.
      + simpl in e. inversion e; auto. inversion H0.
  * epose (H (ELit 0) _). destruct (var_funid_eqb (inr f) x) eqn:P.
    - apply var_funid_eqb_eq in P. subst. simpl. left. auto.
    - constructor 2. unfold subst in e. apply var_funid_eqb_neq in P.
      destruct x.
      + simpl in e. inversion e; auto. inversion H0.
      + simpl in e. remember e as e'. clear Heqe' e. 
        break_match_hyp. apply funid_eqb_eq in Heqb. subst. contradiction.
        inversion e'; auto. inversion H0.
  * constructor. rewrite <- app_comm_cons. apply IHe. intros.
    specialize (H val).
Admitted. *)

(* Theorem sub_implies_scope_single : forall e Γ v,
  ((forall val, (* VALCLOSED val *) VAL Γ ⊢ val -> EXP Γ ⊢ subst v val e) 
 ->
  EXP v::Γ ⊢ e) (* /\
  ((forall val, VALCLOSED val -> VAL Γ ⊢ subst v val e) 
 ->
  VAL v::Γ ⊢ e) *).
Proof.
  einduction e using Exp_ind2; intros; try split; intros.
  * repeat constructor.
  * destruct (var_funid_eqb v0 (inl v)) eqn:P.
    - apply var_funid_eqb_eq in P. subst. unfold subst in H. simpl in H.
      rewrite eqb_refl in H. constructor. left. auto.
    - apply var_funid_eqb_neq in P. unfold subst in H. simpl in H.
      break_match_hyp. break_match_hyp. apply eqb_eq in Heqb. symmetry in Heqb. subst.
      contradiction.
      constructor. right. epose (H (ELit 0) _). inversion e0; auto. inversion H0.
      constructor. right. epose (H (ELit 0) _). inversion e0; auto. inversion H0.
  * destruct (var_funid_eqb v (inr f)) eqn:P.
    - apply var_funid_eqb_eq in P. subst. unfold subst in H. simpl in H.
      rewrite funid_eqb_refl in H. constructor. left. auto.
    - apply var_funid_eqb_neq in P. unfold subst in H. simpl in H.
      break_match_hyp.
      constructor. right. epose (H (ELit 0) _). inversion e0; auto. inversion H0.
      break_match_hyp. apply funid_eqb_eq in Heqb. symmetry in Heqb. subst.
      contradiction.
      constructor. right. epose (H (ELit 0) _). inversion e0; auto. inversion H0.
  * constructor. constructor. rewrite <- app_comm_cons.
    apply IHe0. intros. specialize (H val H0).
    unfold subst in H. break_match_hyp.
    - simpl in H. break_match_hyp.
      + inversion H. subst. inversion H1. subst.
        apply scope_subst_in; eauto. admit. admit.
      + admit.
Abort. *)

(*
Definition magic_γ (Γ Γ' : Env) (n : nat) :=
    if lt_dec n Γ
    then if lt_dec n Γ'
         then Var n
         else Const 0
    else Var Γ'.
Meaning:
  if var is both in Γ and Γ', then it is not modified
  if var is in Γ, but not in Γ', then it is modified to a literal
  if var is not in Γ, then it is replaced by a fresh variable
*)

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




