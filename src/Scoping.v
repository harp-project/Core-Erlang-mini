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
  * intros. simpl. break_match_goal; auto. apply eqb_eq in Heqb. subst. contradiction.
  * intros. simpl. auto.
  * intros. simpl. break_match_goal; auto. rewrite H; auto.
    apply app_not_in; auto. intuition. apply not_in_list_sound in Heqb.
    eapply map_not_in in Heqb. exact (Heqb H1). intro. intros. inversion H2. auto.
  * intros. simpl. break_match_goal; auto. rewrite H; auto.
    repeat apply app_not_in; auto. intro. inversion H1; try congruence. contradiction.
    apply not_in_list_sound in Heqb.
    eapply map_not_in in Heqb. intro. exact (Heqb H1). intro. intros. inversion H1. auto.
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
  * intros. simpl. auto.
  * intros. simpl. break_match_goal; auto. apply funid_eqb_eq in Heqb. subst. contradiction.
  * intros. simpl. rewrite H; auto.
    apply app_not_in; auto. intuition.
    apply inr_inl_map in H1. auto.
  * intros. simpl. break_match_goal; auto.
    rewrite H; auto.
    repeat apply app_not_in; auto.
    intro. inversion H1. inversion H2. apply funid_eqb_neq in Heqb. 1-2: contradiction.
    exact (inr_inl_map x vl).
  * intros. simpl. rewrite H; auto. erewrite scoped_ignores_funsub_helper; eauto.
  * intros. simpl. rewrite H, H0; auto. eapply app_not_in; auto.
      intro. inversion H2. 2: contradiction. inversion H3.
  * intros. simpl. break_match_goal; auto.
    - rewrite H, H0. auto.
      + eapply app_not_in; auto.
        intro. inversion H2. 2: contradiction. inversion H3. subst.
        pose (funid_eqb_refl x). rewrite e2 in Heqb0. inversion Heqb0.
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
  (VAL (Γ ++ Γ') ⊢ e -> forall vals, length vals = length Γ' -> subscoped [] vals -> VAL Γ ⊢ (subst_list Γ' vals e)) /\
  (EXP (Γ ++ Γ') ⊢ e -> forall vals, length vals = length Γ' -> subscoped [] vals -> EXP Γ ⊢ (subst_list Γ' vals e)).
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
    + replace (Γ ++ Γ') with ([] ++ (Γ ++ Γ')); auto. specialize (H1 0 (Nat.lt_0_succ _)).
      simpl in H1. apply scope_ext_app. auto.
  - apply scope_subst; eauto.
    + eapply perm_scoped. exact H. apply Permutation_sym, Permutation_middle.
    + replace (Γ ++ Γ') with ([] ++ (Γ ++ Γ')); auto. specialize (H1 0 (Nat.lt_0_succ _)).
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
  induction e; split; intros; split; intros.
  * unfold subst. destruct v; simpl; constructor; constructor.
  * constructor. constructor.
  * unfold subst. destruct v; simpl; constructor.
  * constructor.
  * unfold subst. destruct v0; simpl.
    - break_match_goal. constructor. apply scope_ext_app. auto.
      inversion H; subst. 2: inversion H1. inversion H2.
      inversion H1. subst. rewrite eqb_refl in Heqb. congruence.
      pose (perm_scoped (Γ' ++ Γ)). destruct a. clear H3. eapply H4. constructor.
      eapply in_app_iff. right. auto. apply Permutation_app. auto. auto.
    - inversion H; subst. 2: inversion H1. inversion H2.
      inversion H1. subst.
      pose (perm_scoped (Γ' ++ Γ)). destruct a. clear H3. eapply H4. constructor.
      eapply in_app_iff. right. auto. apply Permutation_app. auto. auto.
  * constructor. epose (H [] (ELit 0) _). simpl in e. unfold subst in e.
    break_match_hyp.
    - simpl in e. remember e as e'. clear Heqe' e. break_match_hyp.
      + apply eqb_eq in Heqb. constructor. subst. auto.
      + apply eqb_neq in Heqb. constructor 2. inversion e'. auto. inversion H0.
    - simpl in e. constructor 2. inversion e. auto. inversion H0.
  * inversion H.
  * 


Corollary subst_list_preserves_scope : forall Γ,
  (forall e, EXP Γ ⊢ e <->
    forall Γ' vals,
      subscoped Γ' vals -> EXP Γ' ⊢ subst_list Γ vals e) /\
  (forall e, VAL Γ ⊢ e <->
    forall Γ' vals,
      subscoped Γ' vals -> VAL Γ' ⊢ subst_list Γ vals e).
Proof.






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
  

Corollary sub_implies_scope_exp : forall Γ e,
  (forall vals, length vals = length Γ -> subscoped Γ' vals
    -> EXPCLOSED (subst_list Γ vals e))
  ->
  EXP Γ ⊢ e.
Proof.
  intros. pose (alma e Γ). destruct e0, H0, H0, H1. subst. eapply scope_subst_list; auto. specialize (H x0 (eq_sym H0) H1).
  (* induction Γ; intros.
  * unfold subst_list in H. simpl in H. apply (H []); auto.
    intro. intros. inversion H0.
  * pose (alma e a). destruct e0, H0, H0.
    epose (IHΓ (subst a x0 x) _). 
  
  
  unfold subst_list in H. simpl in H. *)
Admitted.





