Require Export ExpManipulation.
Export Relations.Relations.
Export Classes.RelationClasses.

Import ListNotations.

Definition is_value_b (e : Exp) : bool :=
match e with
| ELit _ | EFun _ _ | ERecFun _ _ _ => true
| _ => false
end.

Inductive is_value : Exp -> Prop :=
| ELit_val : forall l, is_value (ELit l)
| EFun_val : forall vl e, is_value (EFun vl e)
| ERecFun_val : forall f vl e, is_value (ERecFun f vl e).

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
Inductive ExpScoped (Γ : nat) : Exp -> Prop :=
| scoped_app exp exps : 
  EXP Γ ⊢ exp ->
  (forall i, i < length exps -> EXP Γ ⊢ nth i exps (ELit 0))
->
  EXP Γ ⊢ EApp exp exps
| scoped_let v e1 e2 :
  EXP Γ ⊢ e1 -> EXP (S Γ) ⊢ e2 
->
  EXP Γ ⊢ ELet v e1 e2
| scoped_letrec f vl b e :
  EXP (S (length vl) + Γ) ⊢ b -> EXP (S Γ) ⊢ e
->
  EXP Γ ⊢ ELetRec f vl b e
| scoped_plus e1 e2 :
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2
->
  EXP Γ ⊢ EPlus e1 e2
| scoped_if e1 e2 e3 :
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e3
->
  EXP Γ ⊢ EIf e1 e2 e3
| scoped_val v :
  VAL Γ ⊢ v -> EXP Γ ⊢ v
with ValScoped (Γ : nat) : Exp -> Prop :=
| scoped_lit lit : VAL Γ ⊢ ELit lit
| scoped_var n v : n < Γ -> VAL Γ ⊢ EVar n v
| scoped_funid n f : n < Γ -> VAL Γ ⊢ EFunId n f
| scoped_fun vl e : EXP (length vl + Γ) ⊢ e -> VAL Γ ⊢ EFun vl e
| scoped_recfun f vl e : EXP (S (length vl) + Γ) ⊢ e -> VAL Γ ⊢ ERecFun f vl e
where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)
and "'VAL' Γ ⊢ e" := (ValScoped Γ e).

Notation "'EXPCLOSED' e" := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v" := (VAL 0 ⊢ v) (at level 5).

Scheme ValScoped_ind2 := Induction for ValScoped Sort Prop
  with ExpScoped_ind2 := Induction for ExpScoped Sort Prop.
Combined Scheme scoped_ind from ValScoped_ind2, ExpScoped_ind2.

Definition subst_preserves (Γ : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> ξ v = inr v.

Theorem subst_preserves_up : forall Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (S Γ) (up_subst ξ).
Proof.
  intros. unfold subst_preserves in *. intros. unfold up_subst. destruct v; auto.
  apply Lt.lt_S_n in H0. apply H in H0. unfold shift. rewrite H0. auto.
Qed.

Global Hint Resolve subst_preserves_up : core.

Corollary subst_preserves_upn : forall n Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (n + Γ) (upn n ξ).
Proof.
  induction n; intros.
  * simpl. auto.
  * simpl. apply subst_preserves_up, IHn. auto.
Qed.

Global Hint Resolve subst_preserves_upn : core.

Theorem subst_preserves_empty ξ : subst_preserves 0 ξ.
Proof. intro. intros. inversion H. Qed.

Global Hint Resolve subst_preserves_empty : core.

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
  (forall e, VAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ] = e) /\
  (forall e, EXP Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ] = e).
Proof.
  apply scoped_ind.
  * intros. reflexivity.
  * intros. specialize (H n l). simpl. rewrite H. auto.
  * intros. specialize (H n l). simpl. rewrite H. auto.
  * intros. simpl. epose (H _ _). rewrite e1. reflexivity.
    Unshelve. apply subst_preserves_upn. auto.
  * intros. simpl. epose (H _ _). rewrite e1. reflexivity.
    Unshelve. apply subst_preserves_up, subst_preserves_upn. auto.
  * intros. simpl. rewrite H; auto. erewrite scoped_ignores_sub_helper; eauto.
  * intros. simpl. rewrite H; auto. rewrite H0; auto.
  * intros. simpl. rewrite H, H0; auto.
    apply subst_preserves_up, subst_preserves_upn. auto.
  * intros. simpl. rewrite H, H0; auto.
  * intros. simpl. rewrite H, H0, H1; auto.
  * intros. eapply H; eauto.
Qed.

Corollary eclosed_ignores_sub :
  forall e ξ,
  EXPCLOSED e -> subst ξ e = e.
Proof.
  intros. eapply scoped_ignores_sub with (Γ := 0); auto.
Qed.

Corollary vclosed_ignores_sub :
  forall e ξ,
  VALCLOSED e -> subst ξ e = e.
Proof.
  intros. pose (scoped_ignores_sub 0). destruct a. apply H0; auto.
Qed.

Global Hint Resolve eclosed_ignores_sub : core.

Global Hint Resolve vclosed_ignores_sub : core.

Theorem scope_ext : forall Γ,
  (forall e, VAL Γ ⊢ e ->  VAL (S Γ) ⊢ e) /\
  forall e, EXP Γ ⊢ e -> EXP (S Γ) ⊢ e.
Proof.
  apply scoped_ind; intros; constructor; try constructor 2; auto.
  all: rewrite Nat.add_succ_r; auto.
Qed.

Lemma scope_ext_Exp : forall {e Γ},
    EXP Γ ⊢ e -> EXP S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

Lemma scope_ext_Val : forall {e Γ},
    VAL Γ ⊢ e -> VAL S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

Theorem app_cons_swap {T : Type} : forall (l l' : list T) (a : T),
  l ++ a::l' = l ++ [a] ++ l'.
Proof.
  firstorder.
Qed.

Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, VAL Γ ⊢ e -> VAL Γ' ⊢ e) /\
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof.
 intros. induction H.
 * intuition.
 * split; intros; eapply scope_ext; eapply IHle; auto. 
Qed.

Definition subscoped (Γ Γ' : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> (match ξ v with
                      | inl exp => VAL Γ' ⊢ exp
                      | inr num => num < Γ'  (* in case of identity subst *)
                      end).

Notation "'SUBSCOPE' Γ ⊢ ξ ∷ Γ'" := (subscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

Definition renscoped (Γ : nat) (Γ' : nat) (ξ : Renaming) : Prop :=
  forall v, v < Γ -> (ξ v) < Γ'.

Notation "'RENSCOPE' Γ ⊢ ξ ∷ Γ'" := (renscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

Lemma renscope_id Γ : RENSCOPE Γ ⊢ id ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve renscope_id : core.

Lemma scope_idsubst Γ : SUBSCOPE Γ ⊢ idsubst ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve scope_idsubst : core.

Lemma upren_scope : forall Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (S Γ) ⊢ upren ξ ∷ (S Γ').
Proof.
  intros.
  unfold renscoped in *.
  intros.
  revert ξ Γ Γ' H H0.
  induction v;
    intros;
    simpl;
    firstorder using Nat.succ_lt_mono.
    lia.
  apply -> Nat.succ_lt_mono. apply H. lia.
Qed.

Lemma uprenn_scope : forall Γ'' Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (Γ'' + Γ) ⊢ uprenn Γ'' ξ ∷ (Γ'' + Γ').
Proof.
  induction Γ''; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply upren_scope. apply IHΓ''. auto.
Qed.

Global Hint Resolve upren_scope : core.
Global Hint Resolve uprenn_scope : core.

Lemma ren_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => Forall (fun e => forall Γ,(EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e)) l);
  try (intros Γ;
  split;
  split;
  intros; cbn; unfold renscoped in *).
  1-4: constructor. 1-2: constructor.
  1, 5, 7: repeat constructor; try apply H0; try inversion H; try inversion H1; auto.
  all: (* this solves around half the goals *)
    try (specialize (H Γ id (renscope_id _)); rewrite idrenaming_is_id in H; apply H).
  all: try (inversion H; inversion H1).
  * constructor. apply H0. inversion H. auto.
  * constructor. constructor. inversion H; inversion H1. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (length vl) _ Γ' ξ H0 v H2). auto.
  * constructor. inversion H. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (length vl) _ Γ' ξ H0 v H1). auto.
  * constructor. constructor. inversion H; inversion H1. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (S (length vl)) _ Γ' ξ H0 v H2). auto.
  * constructor. inversion H. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (S (length vl)) _ Γ' ξ H0 v H1). auto.
  * subst. constructor.
    - eapply IHe; eauto.
    - intros. rewrite indexed_to_forall in IHe0.
      replace (ELit 0) with (rename ξ (ELit 0)) by auto.
      rewrite map_nth. rewrite map_length in H1. eapply IHe0; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. intros. eapply upren_scope; eauto.
  * subst. constructor.
    - eapply IHe1; eauto. intros. eapply upren_scope; eauto.
    - eapply IHe2; eauto. intros. eapply upren_scope; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
    - eapply IHe3; eauto.
  * constructor; eauto.
  * constructor.
Qed.

Lemma ren_preserves_scope_exp : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

Lemma ren_preserves_scope_val : forall e Γ,
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

Lemma up_val : forall Γ v (ξ : Substitution),
  match ξ v with
  | inl exp => VAL Γ ⊢ exp
  | inr num => num < Γ
  end ->
  match up_subst ξ (S v) with
  | inl exp => VAL S Γ ⊢ exp
  | inr num => num < S Γ
  end.
Proof.
  intros. unfold up_subst.
  break_match_hyp.
  * unfold shift. rewrite Heqs. apply -> ren_preserves_scope_val; eauto.
    intro. intros. lia.
  * unfold shift. rewrite Heqs. lia.
Qed.

Lemma up_scope : forall Γ Γ' ξ,
  SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
  SUBSCOPE (S Γ) ⊢ up_subst ξ ∷ (S Γ').
Proof.
  intros.
  unfold subscoped in *.
  intros.
  destruct v; intros.
  * simpl. lia.
  * simpl. unfold shift. break_match_goal. break_match_hyp.
    - inversion Heqs. eapply ren_preserves_scope_val with (Γ:= Γ'); eauto.
      + epose (H v _). rewrite Heqs0 in y. auto. Unshelve. lia.
      + intro. intros. lia.
    - inversion Heqs.
    - break_match_hyp.
      + inversion Heqs.
      + inversion Heqs. subst. epose (H v _). rewrite Heqs0 in y. lia. Unshelve. lia.
Qed.

Global Hint Resolve up_scope : core.

Lemma upn_scope : forall n Γ Γ' ξ,
  SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
  SUBSCOPE (n + Γ) ⊢ upn n ξ ∷ (n + Γ').
Proof.
  induction n; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply up_scope. apply IHn. auto.
Qed.

Global Hint Resolve upn_scope : core.

Lemma cons_scope : forall v Γ Γ' ξ,
    VAL Γ' ⊢ v ->
    SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
    SUBSCOPE (S Γ) ⊢ v.:ξ ∷ Γ'.
Proof.
  intros.
  unfold subscoped in *.
  intros. destruct v0.
  * simpl. auto.
  * simpl. apply H0. lia.
Qed.

Lemma consn_scope : forall (vals : list Exp) Γ Γ' (ξ : Substitution),
    Forall (fun v => VAL Γ' ⊢ v) vals ->
    SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
    SUBSCOPE length vals + Γ ⊢ fold_right (fun v acc => v .: acc) ξ vals ∷ Γ'.
Proof.
  induction vals; intros.
  * simpl. auto.
  * simpl. inversion H. apply cons_scope; auto.
Qed.

Global Hint Resolve cons_scope : core.
Global Hint Resolve consn_scope : core.

(** Substitution is scope-preserving. *)
Lemma subst_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.[ξ]).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => forall Γ,
  Forall (fun e => (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.[ξ])) l);
    try intros Γ;
    try split;
    try split;
    intros.
  all: cbn; unfold subscoped in *.
  1-4: repeat constructor.
  all: try (inversion H); try inversion H1; subst. (* cleaup contradictions *)
  (* prove backward directions: *)
  all: try (specialize (H Γ idsubst (scope_idsubst _)); rewrite idsubst_is_id in H; auto).
  (* forward: *)
  * specialize (H0 n H4). break_match_goal.
    - constructor. auto.
    - constructor. constructor. auto.
  * specialize (H0 n H2). break_match_goal.
    - auto.
    - constructor. auto.
  * specialize (H0 n H4). break_match_goal.
    - constructor. auto.
    - constructor. constructor. auto.
  * specialize (H0 n H2). break_match_goal.
    - auto.
    - constructor. auto.
  * constructor. constructor. eapply IHe; eauto. intros.
    eapply upn_scope; eauto.
  * constructor. eapply IHe; eauto. intros.
    eapply upn_scope; eauto.
  * constructor. constructor. eapply IHe; eauto. intros.
    eapply up_scope; eauto.
  * constructor. eapply IHe; eauto. intros.
    eapply up_scope; eauto.
  * constructor.
    - eapply IHe; eauto.
    - replace (ELit 0) with (subst ξ (ELit 0)) by reflexivity. intros.
      specialize (IHe0 Γ).
      rewrite map_nth. rewrite indexed_to_forall in IHe0. rewrite map_length in H1.
      eapply IHe0; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. apply up_scope. auto.
  * constructor.
    - eapply IHe1; eauto. apply up_scope. auto.
    - eapply IHe2; eauto. apply up_scope. auto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
    - eapply IHe3; eauto.
  * constructor; auto.
  * constructor.
Qed.

Lemma subst_preserves_scope_exp : forall e Γ,
    EXP Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      EXP Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

Lemma subst_preserves_scope_val : forall e Γ,
    VAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      VAL Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

Module SUB_IMPLIES_SCOPE.
  Definition magic_ξ (Γ Γ' : nat) (n : nat) : Exp + nat :=
    if Compare_dec.lt_dec n Γ
    then if Compare_dec.lt_dec n Γ'
         then inr n
         else inl (ELit 0)
    else inr Γ'(* inl (EVar Γ' "x"%string) *).

  Lemma magic_ξ_scope : forall Γ Γ', SUBSCOPE Γ ⊢ magic_ξ Γ Γ' ∷ Γ'.
  Proof.
    unfold subscoped.
    intros.
    unfold magic_ξ.
    repeat destruct Compare_dec.lt_dec; try congruence.
    constructor.
  Qed.

  Lemma up_magic Γ Γ': up_subst (magic_ξ Γ Γ') = magic_ξ (S Γ) (S Γ').
  Proof.
    extensionality x.
    unfold magic_ξ, up_subst.
    destruct x; cbn; auto.
    unfold shift. repeat destruct Compare_dec.lt_dec; auto; lia.
  Qed.

  Lemma upn_magic : forall n Γ Γ', upn n (magic_ξ Γ Γ') = magic_ξ (n + Γ) (n + Γ').
  Proof.
    induction n; intros; simpl; auto.
    rewrite <- up_magic, IHn. auto.
  Qed.

  Lemma magic_ξ_implies_scope : forall e Γ Γ',
      (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e).
  Proof.
    induction e using Exp_ind2 with
    (Q := fun l =>
      Forall (fun e => forall Γ Γ', (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e)) l);
      try intros Γ Γ';
      try split;
      intros;
      try cbn in H.
    1-2, 4, 6, 8: constructor.
    constructor.
    * break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * inversion H. inversion H0. subst.
      eapply IHe. rewrite upn_magic in H1. eauto.
    * constructor. constructor. break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * constructor. constructor. break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * constructor. constructor. inversion H. inversion H0. subst.
      eapply IHe. replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                          (upn (S (length vl)) ((magic_ξ Γ Γ'))) in H3 by reflexivity.
      rewrite upn_magic in H3. eauto.
    * constructor. constructor. inversion H. inversion H0. subst.
      eapply IHe. replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                          (upn (S (length vl)) ((magic_ξ Γ Γ'))) in H3 by reflexivity.
      rewrite upn_magic in H3. eauto.
    * constructor. inversion H. subst.
      eapply IHe. replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                          (upn (S (length vl)) ((magic_ξ Γ Γ'))) in H1 by reflexivity.
      rewrite upn_magic in H1. eauto.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe; eauto.
      - replace (ELit 0) with (subst (magic_ξ Γ Γ') (ELit 0)) in H3 by reflexivity.
        intros. erewrite <- map_length in H4. specialize (H3 i H4).
        rewrite map_nth in H3. subst. rewrite indexed_to_forall in IHe0.
        rewrite map_length in H4.
        eapply IHe0; eauto.
    * inversion H.
    * inversion H. 2: inversion H0. subst. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto. rewrite up_magic in H4. eauto.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
        replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                (upn (S (length vl)) (magic_ξ Γ Γ')) in H2 by reflexivity.
        rewrite upn_magic in H2. exact H2.
      - eapply IHe2; eauto.
        rewrite up_magic in H5. exact H5.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
      - eapply IHe3; eauto.
    * inversion H.
    * constructor; auto.
    * constructor.
  Qed.

  Lemma sub_implies_scope_exp : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ e.[ξ]) ->
      EXP Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ e.[ξ]) ->
      VAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Definition magic_ξ_2 Γ' :=
    fun n =>
      if Compare_dec.lt_dec n Γ'
      then idsubst n
      else if Nat.eq_dec n Γ'
           then inl (ELit 0)
           else idsubst (pred n).

  Lemma up_magic_2 : forall Γ,
      up_subst (magic_ξ_2 Γ) = magic_ξ_2 (S Γ).
  Proof.
    intros.
    unfold magic_ξ_2.
    extensionality x.
    unfold up_subst, shift, idsubst.
    destruct x; auto.
    simpl.
    unfold Init.Nat.pred.
    repeat destruct Compare_dec.lt_dec; auto; destruct Nat.eq_dec; auto; try lia.
    f_equiv. destruct x; lia.
  Qed.

  Lemma upn_magic_2 : forall n Γ,
    upn n (magic_ξ_2 Γ) = magic_ξ_2 (n + Γ).
  Proof.
    induction n; intros; cbn; auto.
    * rewrite <- up_magic_2, IHn. auto.
  Qed.

  Lemma magic_const : magic_ξ_2 0 = ELit 0 .: idsubst.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst. inversion l.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto. lia.
  Qed.

  Lemma magic_ξ_magic_ξ_2 : forall e Γ',
      (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
      (VAL Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']).
  Proof.
    induction e using Exp_ind2 with
      (Q := fun l => forall Γ', Forall (fun e =>
        (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
        (VAL Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ'])
      ) l); intros; cbn; auto.
    * unfold magic_ξ_2, magic_ξ, idsubst.
      repeat destruct Compare_dec.lt_dec; try destruct Nat.eq_dec; auto.
      lia. lia. lia. split; intros; inversion H. inversion H0. all: subst.
      all : lia.
    * unfold magic_ξ_2, magic_ξ, idsubst.
      repeat destruct Compare_dec.lt_dec; try destruct Nat.eq_dec; auto.
      lia. lia. lia. split; intros; inversion H. inversion H0. all: subst.
      all : lia.
    * rewrite upn_magic, upn_magic_2.
      replace (length vl + S Γ') with (S (length vl + Γ')) by lia.
      specialize (IHe (length vl + Γ')). destruct IHe. split; intros.
      - rewrite H; auto. inversion H1. inversion H2. auto.
      - rewrite H; auto. inversion H1. subst. auto.
    * rewrite upn_magic, up_magic, upn_magic_2, up_magic_2.
      replace (S (length vl + S Γ')) with (S (S (length vl) + Γ')) by lia.
      specialize (IHe (S (length vl + Γ'))). destruct IHe. split; intros.
      - rewrite <- H; auto. inversion H1. inversion H2. auto.
      - rewrite <- H; auto. inversion H1. subst. auto.
    * specialize (IHe Γ'). specialize (IHe0 Γ'). destruct IHe.
      split; intros; inversion H1; subst. 2: inversion H2. rewrite H; auto.
      apply Forall_and_inv in IHe0. destruct IHe0. erewrite map_ext_Forall. reflexivity.
      rewrite indexed_to_forall in *. intros. apply H2; auto.
      replace (ELit 0) with ((ELit 0).[magic_ξ_2 Γ']) in H5 by reflexivity.
      rewrite map_length in H5. specialize (H5 i H6). rewrite map_nth in H5.
      exact H5.
    * specialize (IHe1 Γ'). specialize (IHe2 (S Γ')). destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4.
      rewrite H; auto. rewrite up_magic, up_magic_2, H1; auto.
      now rewrite up_magic_2 in H8.
    * specialize (IHe1 (length vl + S Γ')). specialize (IHe2 (S Γ')).
      destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4.
      rewrite upn_magic, upn_magic_2, up_magic, up_magic_2.
      replace (S (Datatypes.length vl + Γ')) with (Datatypes.length vl + S Γ') by lia.
      rewrite H; auto. rewrite up_magic, up_magic_2, H1 in *; auto.
      rewrite upn_magic_2, up_magic_2 in H6. now rewrite <- Nat.add_succ_comm.
    * specialize (IHe1 Γ'). specialize (IHe2 Γ'). destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4. now rewrite H, H1.
    * specialize (IHe1 Γ'). specialize (IHe2 Γ'). specialize (IHe3 Γ').
      destruct IHe1, IHe2, IHe3.
      split; intros; inversion H5; subst. 2: inversion H6. now rewrite H, H1, H3.
  Unshelve. exact (ELit 0).
  Qed.

  Lemma magic_ξ_magic_ξ_2_closed : forall e,
      (EXPCLOSED e.[ELit 0/] ->
       e.[magic_ξ 1 0] = e.[ELit 0 .: idsubst]) /\
      (VALCLOSED e.[ELit 0/] ->
       e.[magic_ξ 1 0] = e.[ELit 0 .: idsubst]).
  Proof.
    intros.
    rewrite <- magic_const.
    apply magic_ξ_magic_ξ_2.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e,
      EXPCLOSED e.[ELit 0/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H0; auto.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e,
      VALCLOSED e.[ELit 0/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H1; auto.
  Qed.
End SUB_IMPLIES_SCOPE.

Definition subst_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition subst_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition subst_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition subst_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.

Lemma upn_Var : forall (Γ : nat) (ξ : Substitution) (v : nat),
    v < Γ -> upn Γ ξ v = inr v.
Proof.
  intros Γ ξ.
  induction Γ;
    intros.
  + inversion H.
  + simpl. destruct v.
    * simpl. auto.
    * simpl. unfold shift. rewrite IHΓ. 2: lia. auto.
Qed.

Corollary upn_ignores_sub : forall e Γ ξ,
     (EXP Γ ⊢ e -> e.[upn Γ ξ] = e) /\
     (VAL Γ ⊢ e -> e.[upn Γ ξ] = e).
Proof.
  intros. split; intros.
  * eapply scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
  * pose (scoped_ignores_sub Γ). destruct a. apply H0. auto.
    intro. intros. apply upn_Var. auto.
Qed.

Lemma escoped_ignores_sub : forall e Γ ξ,
    EXP Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve escoped_ignores_sub : core.

Lemma vscoped_ignores_sub : forall e Γ ξ,
    VAL Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve vscoped_ignores_sub : core.

Lemma eclosed_sub_closed : forall v ξ,
    EXPCLOSED v -> EXPCLOSED v.[ξ].
Proof.
  intros.
  rewrite eclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve eclosed_sub_closed : core.

Lemma vclosed_sub_closed : forall v ξ,
    VALCLOSED v -> VALCLOSED v.[ξ].
Proof.
  intros.
  rewrite vclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve vclosed_sub_closed : core.

(* FrameStack *)
(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)
(* Section stack_machine_semantics. *)
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (* (p : is_value v)  *) (l1 l2 : list Exp) (* (p2 : forall e, In e l2 -> is_value e) *) (** Can be problematic *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (* (p : is_value v) *) (* v + □ *)
| FIf (e2 e3 : Exp) (* if □ then e2 else e3 *).

Definition FrameStack := list Frame.

Lemma empty_is_value : forall e, In e [] -> is_value e. Proof. firstorder. Qed.
Lemma step_value : forall l v,
  (forall e, In e l -> is_value e) -> is_value v
->
  (forall e, In e (l ++ [v]) -> is_value e).
Proof.
  intros. apply in_app_or in H1. destruct H1.
  * apply H. auto.
  * firstorder. subst. auto.
Qed.

Inductive FCLOSED : Frame -> Prop :=
| fclosed_app1 l:
  Forall (fun e => EXPCLOSED e) l
->
  FCLOSED (FApp1 l)
| fclosed_app2 v (* p *) l1 l2 (* p2 *):
  VALCLOSED v -> Forall (fun e => EXPCLOSED e) l1 -> Forall (fun e => VALCLOSED e) l2
->
  FCLOSED (FApp2 v (* p *) l1 l2 (* p2 *))
| fclosed_let e2 v :
  EXP 1 ⊢ e2
->
  FCLOSED (FLet v e2)
| fclosed_plus1 e2:
  EXPCLOSED e2
->
  FCLOSED (FPlus1 e2)
| fclosed_plus2 v1 (* p *):
  VALCLOSED v1
->
  FCLOSED (FPlus2 v1 (* p *))
| fclosed_if e2 e3:
  EXPCLOSED e2 -> EXPCLOSED e3
->
  FCLOSED (FIf e2 e3).

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.

Lemma scoped_list_subscoped :
  forall vals Γ ξ Γ', Forall (fun v => VAL Γ ⊢ v) vals -> SUBSCOPE Γ' ⊢ ξ ∷ Γ ->
  SUBSCOPE length vals + Γ' ⊢ list_subst vals ξ ∷ Γ.
Proof.
  induction vals; intros; simpl; auto.
  simpl. inversion H. intro. intros. destruct v.
  * simpl. apply H3.
  * simpl. specialize (IHvals _ _ _ H4 H0 v). apply IHvals. lia.
Qed.

Lemma scoped_list_idsubst :
  forall vals Γ, Forall (fun v => VAL Γ ⊢ v) vals ->
  SUBSCOPE length vals ⊢ list_subst vals idsubst ∷ Γ.
Proof.
  induction vals; intros. simpl.
  unfold idsubst. intro. intros. inversion H0.
  simpl. inversion H. intro. intros. destruct v.
  * simpl. apply H2.
  * simpl. apply IHvals; auto. lia.
Qed.

