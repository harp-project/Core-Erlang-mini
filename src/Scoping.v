Require Export ExpSyntax.
Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FunctionalExtensionality.

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
Check scoped_ind.

Definition subst_preserves (Γ : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> ξ v = inr v.

Theorem subst_preserves_up : forall Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (S Γ) (up_subst ξ).
Proof.
  intros. unfold subst_preserves in *. intros. unfold up_subst. destruct v; auto.
  apply Lt.lt_S_n in H0. apply H in H0. rewrite H0. auto.
Qed.

Hint Resolve subst_preserves_up.

Corollary subst_preserves_upn : forall n Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (n + Γ) (upn n ξ).
Proof.
  induction n; intros.
  * simpl. auto.
  * simpl. apply subst_preserves_up, IHn. auto.
Qed.

Hint Resolve subst_preserves_upn.

Theorem subst_preserves_empty ξ : subst_preserves 0 ξ.
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

Hint Resolve renscope_id.

Lemma scope_idsubst Γ : SUBSCOPE Γ ⊢ idsubst ∷ Γ.
Proof.
  firstorder.
Qed.

Hint Resolve scope_idsubst.

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

Hint Resolve upren_scope.
Hint Resolve uprenn_scope.

Theorem idren_is_id : forall e,
  rename id e = e.
Proof.
  induction e; intros.
  (* TODO *)
Admitted.

Theorem idsubst_is_id : forall e,
  subst idsubst e = e.
Proof.
  induction e; intros.
  (* TODO *)
Admitted.

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
    try (specialize (H Γ id (renscope_id _)); rewrite idren_is_id in H; apply H).
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
    - intros. Search Forall. rewrite indexed_to_forall in IHe0.
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
  * apply -> ren_preserves_scope_val; eauto.
    intro. intros. lia.
  * lia.
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
  * simpl. break_match_goal. break_match_hyp.
    - inversion Heqs. eapply ren_preserves_scope_val with (Γ:= Γ'); eauto.
      + epose (H v _). rewrite Heqs0 in y. auto. Unshelve. lia.
      + intro. intros. lia.
    - inversion Heqs.
    - break_match_hyp.
      + inversion Heqs.
      + inversion Heqs. subst. epose (H v _). rewrite Heqs0 in y. lia. Unshelve. lia.
Qed.

Hint Resolve up_scope.

Lemma upn_scope : forall n Γ Γ' ξ,
  SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
  SUBSCOPE (n + Γ) ⊢ upn n ξ ∷ (n + Γ').
Proof.
  induction n; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply up_scope. apply IHn. auto.
Qed.

Hint Resolve upn_scope.

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

Hint Resolve cons_scope.

(** Substitution is scope-preserving. *)
Lemma sub_preserves_scope : forall e Γ,
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

Lemma sub_preserves_scope_exp : forall e Γ,
    EXP Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      EXP Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply sub_preserves_scope.
Qed.

Lemma sub_preserves_scope_val : forall e Γ,
    VAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      VAL Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply sub_preserves_scope.
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
    repeat destruct Compare_dec.lt_dec; auto; lia.
  Qed.

  Lemma magic_ξ_implies_scope : forall e Γ Γ',
      (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e).
  Proof.
    induction e;
      intros Γ Γ';
      split;
      intros;
      cbn in H;
      try invert_scoped H;
      try solve
          [constructor;
           let e := match goal with
                    | [ |- EXP _ ⊢ ?e ] => e
                    | [ |- VAL _ ⊢ ?e ] => e
                    end in
           match goal with
           | [IHe : forall (Γ Γ' : Env), (_ -> EXP Γ ⊢ e) /\ (_ -> VAL Γ ⊢ e),
                H : VAL _ ⊢ e.[magic_ξ Γ Γ'] |- _ ] =>
             eapply IHe in H; try eassumption; auto
           | [IHe : forall (Γ Γ' : Env), (_ -> EXP Γ ⊢ e) /\ (_ -> VAL Γ ⊢ e),
                H : EXP _ ⊢ e.[magic_ξ Γ Γ'] |- _ ] =>
             eapply IHe in H; try eassumption; auto
           end];
    auto.
    - cbn in *.
      unfold magic_ξ in H.
      repeat destruct lt_dec;
        auto.
      inversion H; subst.
      inversion H0.
      auto.
    - cbn in *.
      unfold magic_ξ in H.
      repeat destruct lt_dec;
        auto.
      inversion H.
      auto.
    - constructor.
      constructor.
      eapply IHe.
      rewrite <- up_magic.
      eauto.
    - constructor.
      eapply IHe.
      rewrite <- up_magic.
      eauto.
    - constructor;
        firstorder idtac.
      eapply IHe0.
      rewrite <- up_magic.
      eauto.
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
      if lt_dec n Γ'
      then Var n
      else if Nat.eq_dec n Γ'
           then Const 0
           else Var (pred n).

  Lemma up_magic_2 : forall Γ,
      up (magic_ξ_2 Γ) = magic_ξ_2 (S Γ).
  Proof.
    intros.
    unfold magic_ξ_2.
    extensionality x.
    unfold up.
    unfold ".:".
    destruct x; auto.
    simpl.
    unfold Init.Nat.pred.
    repeat destruct lt_dec;
      destruct (Nat.eq_dec x Γ);
      destruct x;
      subst;
      cbn;
      auto.
  Qed.

  Lemma magic_const : magic_ξ_2 0 = Const 0 .: ids.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct lt_dec; auto.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto.
  Qed.

  Lemma foo : forall e Γ',
      (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
      (VAL Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']).
  Proof.
    induction e;
      split;
      intros Hscope;
      cbn;
      cbn in Hscope;
      try invert_scoped Hscope;
      auto;
      try rewrite up_magic_2 in *;
      try rewrite up_magic in *;
      try solve
          [repeat
             match goal with
             | [ IHe : forall (Γ' : Env), (EXP Γ' ⊢ ?e.[_] -> _) /\ (VAL Γ' ⊢ ?e.[_] -> _),
                   H : VAL _ ⊢ ?e.[_]
                   |- _] => apply IHe in H
             | [ IHe : forall (Γ' : Env), (EXP Γ' ⊢ ?e.[_] -> _) /\ (VAL Γ' ⊢ ?e.[_] -> _),
                   H : EXP _ ⊢ ?e.[_]
                   |- _] => apply IHe in H
             end;
           f_equal;
           auto].
    - unfold magic_ξ, magic_ξ_2 in *;
        cbn in *;
        repeat destruct lt_dec; auto;
          destruct (Nat.eq_dec v Γ'); auto;
            destruct v, Γ';
            inversion Hscope;
            try inversion H;
            subst;
            cbn;
            auto.
    - asimpl in Hscope.
      unfold magic_ξ, magic_ξ_2 in *.
      repeat destruct lt_dec;
        repeat destruct Nat.eq_dec;
        inversion Hscope;
        auto.
  Qed.

  Lemma bar : forall e,
      (ECLOSED e.[Const 0/] ->
       e.[magic_ξ 1 0] = e.[Const 0 .: ids]) /\
      (VCLOSED e.[Const 0/] ->
       e.[magic_ξ 1 0] = e.[Const 0 .: ids]).
  Proof.
    intros.
    rewrite <- magic_const.
    apply foo.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e,
      ECLOSED e.[Const 0/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (bar e).
    rewrite H0; auto.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e,
      VCLOSED e.[Const 0/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (bar e).
    rewrite H1; auto.
  Qed.
End SUB_IMPLIES_SCOPE.

Definition sub_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition sub_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition sub_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition sub_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.

Lemma upn_Var : forall (Γ : Env) (ξ : var -> Expr) (v : var),
    v < Γ -> upn Γ ξ v = Var v.
Proof.
  intros Γ ξ.
  induction Γ;
    intros.
  + auto.
  + rewrite iterate_S.
    destruct v;
      asimpl;
      auto.
    rewrite IHΓ;
      auto.
Qed.

Lemma scoped_ignores_sub : forall e Γ ξ,
     (EXP Γ ⊢ e -> e.[upn Γ ξ] = e) /\
     (VAL Γ ⊢ e -> e.[upn Γ ξ] = e).
Proof.
  induction e;
    cbn;
    split;
    intros;
    invert_scoped H;
    auto using upn_Var;
    try solve
        [repeat
           match goal with
           | [ IHe : forall (Γ : Env) (ξ : var -> Expr), (EXP Γ ⊢ ?e -> _) /\ (VAL Γ ⊢ ?e -> _),
                 H : VAL _ ⊢ ?e
                 |- _] => eapply IHe in H
           | [ IHe : forall (Γ : Env) (ξ : var -> Expr), (EXP Γ ⊢ ?e -> _) /\ (VAL Γ ⊢ ?e -> _),
                 H : EXP _ ⊢ ?e
                 |- _] => eapply IHe in H
           end;
         f_equal;
         eauto].
Qed.

Lemma escoped_ignores_sub : forall e Γ ξ,
    EXP Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.  
  intros.
  eapply scoped_ignores_sub in H.
  eauto.
Qed.
Hint Resolve escoped_ignores_sub.

Lemma vscoped_ignores_sub : forall e Γ ξ,
    VAL Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.
  intros.
  eapply scoped_ignores_sub in H.
  eauto.
Qed.
Hint Resolve vscoped_ignores_sub.

Lemma eclosed_ignores_sub : forall e ξ,
     ECLOSED e -> e.[ξ] = e.
Proof.
  intros.
  replace (e.[ξ]) with (e.[upn 0 ξ])
    by (rewrite upn0; auto).
  auto.
Qed.
Hint Resolve eclosed_ignores_sub.

Lemma vclosed_ignores_sub : forall e ξ,
     VCLOSED e -> e.[ξ] = e.
Proof.
  intros.
  replace (e.[ξ]) with (e.[upn 0 ξ])
    by (rewrite upn0; auto).
  auto.
Qed.
Hint Resolve vclosed_ignores_sub.

Lemma eclosed_sub_closed : forall v ξ,
    ECLOSED v -> ECLOSED v.[ξ].
Proof.
  intros.
  rewrite eclosed_ignores_sub;
    auto.
Qed.
Hint Resolve eclosed_sub_closed.

Lemma vclosed_sub_closed : forall v ξ,
    VCLOSED v -> VCLOSED v.[ξ].
Proof.
  intros.
  rewrite vclosed_ignores_sub;
    auto.
Qed.
Hint Resolve vclosed_sub_closed.

(* Continuations *)

Inductive Kont : Type :=
| Knil : Kont
| Kcons : Expr -> Kont -> Kont.

Infix "-:" := Kcons (at level 60, right associativity).

Lemma Kont_eq_dec : forall (K K' : Kont),
    decidable (K = K').
Proof.
  unfold decidable.
  induction K;
    destruct K';
    intros;
    try solve [intuition auto].
  destruct (Expr_eq_dec e e0);
    subst;
    revgoals.
  { right.
    contradict n.
    inversion n; subst; auto.
  }
  specialize (IHK K').
  inversion IHK; subst.
  + left; auto.
  + right.
    contradict H.
    inversion H.
    auto.
Qed.

Reserved Notation "'KCLOSED' K" (at level 69).

Inductive KontScoped : forall K, Prop :=
| KontScoped_nil :
    KCLOSED Knil
| KontScoped_cons : forall K e,
    EXP 1 ⊢ e ->
    KCLOSED K ->
    KCLOSED e -: K
where
"'KCLOSED' K" := (KontScoped K).

Hint Constructors KontScoped.

Theorem var_not_closed1 n v : ~ VALCLOSED (EVar n v).
Proof. intro. inversion H. inversion H1. Qed.

Hint Resolve var_not_closed1.

Theorem var_not_closed2 n v : ~ EXPCLOSED (EVar n v).
Proof. intro. inversion H. eapply var_not_closed1. eauto. Qed.

Hint Resolve var_not_closed2.

Theorem funid_not_closed1 n f : ~ VALCLOSED (EFunId n f).
Proof. intro. inversion H. inversion H1. Qed.

Hint Resolve funid_not_closed1.

Theorem funid_not_closed2 n f : ~ EXPCLOSED (EFunId n f).
Proof. intro. inversion H. eapply funid_not_closed1. eauto. Qed.

Hint Resolve funid_not_closed2.

(* Theorem restrict_in : forall l ξ v,
  In v l -> (ξ -- l) v = idsubst v.
Proof.
  intros. unfold "--". apply in_list_sound in H. rewrite H. auto.
Qed.

Theorem restrict_not_in : forall l ξ v,
  ~In v l -> (ξ -- l) v = ξ v.
Proof.
  intros. unfold "--". apply not_in_list_sound in H. rewrite H. auto.
Qed. *)




Theorem subscoped_preserves_app : forall ξ Γ Γ',
  subscoped Γ Γ' ξ -> (subscoped (S Γ) (S Γ') (up_subst ξ)).
Proof.
  intros. intro. intros. break_match_goal.
  * unfold subscoped in H.
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


(** Actually, this was not needed in the end, however it is useful to have it *)
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

Opaque app.

Lemma magic_ξ_implies_scope : forall e Γ Γ' name 
  (p1 : ~In name Γ) (p2 : ~In name Γ') (p3 : ~In name (names e)),
  (EXP Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> EXP Γ ⊢ e) /\
  (VAL Γ' ⊢ subst (magic_ξ Γ Γ' name) e -> VAL Γ ⊢ e).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => Forall (fun e => forall Γ Γ' name
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
  * constructor. constructor.
    simpl in H. inversion H. inversion H0. subst.
    erewrite magic_ξ_app_eq in H3. eapply (IHe _ (Γ' ++ map inl vl)). 4: exact H3. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. simpl in H. inversion H. subst.
    erewrite magic_ξ_app_eq in H1. eapply (IHe _ (Γ' ++ map inl vl)). 4: exact H1. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. constructor.
    simpl in H. inversion H. inversion H0. subst.
    erewrite magic_ξ_app_eq in H3. eapply (IHe _ (Γ' ++ inr f :: map inl vl)). 4: exact H3. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * constructor. simpl in H. inversion H. subst.
    erewrite magic_ξ_app_eq in H1. eapply (IHe _ (Γ' ++ inr f :: map inl vl)). 4: exact H1. all: eauto.
    all: try apply app_not_in; auto. all: apply app_in_not in p3; destruct p3; auto.
  * inversion H. 2: inversion H0. subst. simpl in p3. app_in_not_tac. destruct p3.
    apply notin_flat_map_Forall in H1. rewrite indexed_to_forall in IHe0, H1. constructor.
    - eapply IHe. 4: exact H2. all: auto.
    - intros. rewrite map_length in *. specialize (H3 i H4).
      replace (ELit 0) with (subst (magic_ξ Γ Γ' name) (ELit 0)) in H3 by reflexivity.
      rewrite map_nth in H3. eapply IHe0. 5: exact H3. all: auto.
  * inversion H.
  * inversion H. 2: inversion H0. subst. simpl names in p3. app_in_not_tac. destruct p3.
    app_in_not_tac. destruct H1. constructor.
    - eapply IHe1. 4: exact H2. all: auto.
    - erewrite magic_ξ_app_eq in H4. eapply IHe2. 4: exact H4. all: try apply app_not_in; auto.
  * inversion H.
  * inversion H. 2: inversion H0. subst. simpl names in p3. app_in_not_tac. destruct p3.
    app_in_not_tac. destruct H1. constructor.
    - erewrite magic_ξ_app_eq in H2. eapply IHe1. 4: exact H2. all: try apply app_not_in; auto.
    - erewrite magic_ξ_app_eq in H5.
      replace (inr f :: map inl vl) with ([inr f] ++ map inl vl) in H0 by reflexivity. app_in_not_tac.
      destruct H0. eapply IHe2. 4: exact H5. all: try apply app_not_in; auto.
  * inversion H.
  * inversion H. 2: inversion H0. subst. simpl in p3. app_in_not_tac. destruct p3.
    constructor.
    - eapply IHe1. 4: exact H2. all: auto.
    - eapply IHe2. 4: exact H3. all: auto.
  * inversion H.
  * inversion H. 2: inversion H0. subst. simpl in p3. app_in_not_tac. destruct p3.
    app_in_not_tac. destruct H1.
    constructor.
    - eapply IHe1. 4: exact H3. all: auto.
    - eapply IHe2. 4: exact H4. all: auto.
    - eapply IHe3. 4: exact H5. all: auto.
  * inversion H.
  * constructor. apply IHe. apply IHe0.
  * constructor.
Qed.

Transparent app.

Theorem sub_implies_scope_exp :
  forall e Γ Γ',
  (forall ξ, subscoped Γ Γ' ξ -> EXP Γ' ⊢ subst ξ e) -> EXP Γ ⊢ e.
Proof.
  intros. pose (fresh_is_fresh (Γ ++ Γ' ++ (names e))).
  app_in_not_tac. destruct n. app_in_not_tac. destruct H1.
  eapply magic_ξ_implies_scope with (name := inl (new_fresh (Γ ++ Γ' ++ (names e)))).
  4: apply H; apply magic_ξ_scope.
  all: auto.
Qed.

Lemma eval_list_length : forall l clock vl, eval_list (eval clock) l = Res vl -> length l = length vl.
Proof.
  induction l; intros.
  * simpl in H. inversion H. auto.
  * simpl in H. repeat break_match_hyp; try congruence. inversion H. simpl. erewrite IHl; eauto.
Qed.

Lemma eval_scoped_list l : forall v1 Γ clock,
  (forall e v : Exp, eval clock e = Res v -> forall Γ : list VarFunId, EXP Γ ⊢ e -> VAL Γ ⊢ v) ->
  (eval_list (eval clock) l = Res v1) ->
  (forall i : nat, i < Datatypes.length l -> EXP Γ ⊢ nth i l (ELit 0))
->
  forall i : nat, i < length l -> VAL Γ ⊢ nth i v1 (ELit 0)
  .
Proof.
  induction l; intros.
  inversion H2. simpl in H0. repeat break_match_hyp; try congruence. inversion H0. subst.
  destruct i.
  * simpl. eapply H in Heqr; eauto. apply (H1 0). auto.
  * simpl in H2. apply Lt.lt_S_n in H2. simpl. eapply IHl; eauto. intros. apply (H1 (S i0)). simpl. lia.
Qed.

Theorem extension_subscoped :
  forall l ξ Γ Γ', subscoped Γ Γ' ξ -> forall vals, length vals = length l -> Forall (fun v => VAL Γ' ⊢ v) vals -> subscoped (Γ ++ l) Γ' (ξ[[::= combine l vals]]).
Proof.
  induction l; intros.
  * cbn. rewrite app_nil_r. auto.
  * apply eq_sym, element_exist in H0 as H0'. destruct H0', H2. subst.
    cbn. replace ((fold_left (fun (ξ' : Substitution) '(x1, e) => ξ' [[x1 ::= e]]) (combine l x0) (ξ [[a ::= x]]))) with ((ξ[[ a ::= x ]]) [[ ::= combine l x0]]) by reflexivity. simpl in H0. inversion H0. inversion H1. subst.
    epose (IHl (ξ[[a ::= x]]) (Γ ++ [a]) Γ' _ x0 (eq_sym H3) H6). rewrite <- app_assoc in s. simpl in s. auto.
Unshelve.
  unfold subscoped. intros. unfold extend_subst. break_match_goal.
  - auto.
  - apply H. apply in_app_iff in H2. destruct H2; auto. inversion H2; apply var_funid_eqb_neq in Heqb. congruence. inversion H4.
Qed.

Theorem eval_scoped_exp : forall clock e v,
  eval clock e = Res v -> forall Γ, EXP Γ ⊢ e -> VAL Γ ⊢ v.
Proof.
  induction clock; intros. inversion H.
  destruct e; inversion H; clear H; subst.
  * constructor.
  * inversion H0. auto.
  * inversion H0. auto.
  * repeat break_match_hyp; try congruence; subst.
    - inversion H0. 2: inversion H. subst. eapply IHclock in H3. 2: eauto.
      pose (eval_scoped_list _ _ _ _ IHclock Heqr0 H4).
      inversion H3. subst. pose (subst_preserves_scope_rev e0 (Γ ++ map inl vl)). destruct a. clear H5.
      specialize (H H1 Γ (idsubst [[ ::= combine (map inl vl) v1]])).
      assert (subscoped (Γ ++ map inl vl) Γ (idsubst [[ ::= combine (map inl vl) v1]])). {
        Search subscoped. apply extension_subscoped; auto. apply idsubst_scoped. rewrite map_length.
        apply Nat.eqb_eq in Heqb. auto. rewrite Forall_nth. intros. apply Nat.eqb_eq in Heqb. 
        apply eval_list_length in Heqr0 as H'. rewrite H' in v0.
        specialize (v0 i H5). Search nth. erewrite nth_indep; eauto.
      }
      specialize (H H5). eapply IHclock; eauto.
    - inversion H0. 2: inversion H. subst. eapply IHclock in H3. 2: eauto.
      pose (eval_scoped_list _ _ _ _ IHclock Heqr0 H4).
      inversion H3. subst. pose (subst_preserves_scope_rev e0 (Γ ++ inr f :: map inl vl)). destruct a. clear H5.
      specialize (H H1 Γ (idsubst [[ ::= combine (inr f :: (map inl vl)) (ERecFun f vl e0 :: v1)]])).
      assert (subscoped (Γ ++ inr f :: map inl vl) Γ (idsubst [[ ::= combine (inr f :: (map inl vl)) (ERecFun f vl e0 :: v1)]])). {
        Search subscoped. apply extension_subscoped; auto. apply idsubst_scoped. simpl. rewrite map_length.
        apply Nat.eqb_eq in Heqb. auto. rewrite Forall_nth. intros. apply Nat.eqb_eq in Heqb. 
        apply eval_list_length in Heqr0 as H'. rewrite H' in v0. destruct i.
        + simpl. auto.
        + simpl in H5. apply Lt.lt_S_n in H5. specialize (v0 i H5). Search nth. erewrite nth_indep; eauto. simpl. lia.
      }
      specialize (H H5). eapply IHclock; eauto.
  * break_match_hyp; try congruence.
    inversion H0. 2: inversion H. subst.
    pose (IHclock _ _ Heqr _ H3). pose (subst_preserves_scope_rev e2 (Γ ++ [inl v0])). destruct a.
    clear H1. specialize (H H5 Γ (idsubst[[inl v0 ::= v1]])).
    assert (subscoped (Γ ++ [inl v0]) Γ (idsubst [[inl v0 ::= v1]])).
    { unfold subscoped. intros. unfold idsubst, extend_subst. break_match_goal.
      - auto.
      - destruct v3; constructor; apply in_app_iff in H1; destruct H1; auto.
        all: apply var_funid_eqb_neq in Heqb; inversion H1; try congruence; inversion H4. }
    specialize (H H1). eapply IHclock in H2; eauto.
  * inversion H0. 2: inversion H. subst.
    pose (subst_preserves_scope_rev e2 (Γ ++ [inr f])). destruct a. clear H1.
    specialize (H H6 Γ (idsubst [[inr f ::= ERecFun f vl e1]])).
    assert (subscoped (Γ ++ [inr f]) Γ (idsubst [[inr f ::= ERecFun f vl e1]])). {
      unfold subscoped. intros. unfold idsubst, extend_subst. break_match_goal.
      - constructor. auto.
      - destruct v0; constructor; apply in_app_iff in H1; destruct H1; auto.
        all: apply var_funid_eqb_neq in Heqb; inversion H1; try congruence; inversion H4.
    }
    specialize (H H1). eapply IHclock in H2; eauto.
  * inversion H0. 2: inversion H. subst. repeat break_match_hyp; try congruence.
    inversion H2. constructor.
  * inversion H0. 2: inversion H. subst. break_match_hyp; try congruence. destruct v0. destruct l.
    all: eapply IHclock in H2; eauto.
Qed.

(*
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (p : is_value v) (l1 l2 : list Exp) (p2 : forall e, In e l2 -> is_value e) (** Can be problematic *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (p : is_value v) (* v + □ *)
| FIf (e2 e3 : Exp) (* if □ then e2 else e3 *).
*)
(**
  FrameStacks are closed, when all of their frames are closed.
*)
Inductive FCLOSED : FrameStack -> Prop :=
| fclosed_nil : FCLOSED []
| fclosed_app1 l xs:
  Forall (fun e => EXPCLOSED e) l ->
  FCLOSED xs
->
  FCLOSED (FApp1 l::xs)
| fclosed_app2 v p l1 l2 p2 xs:
  VALCLOSED v -> Forall (fun e => EXPCLOSED e) l1 -> Forall (fun e => VALCLOSED e) l2 ->
  FCLOSED xs
->
  FCLOSED (FApp2 v p l1 l2 p2::xs)
| fclosed_let v e2 xs :
  EXP [inl v] ⊢ e2 ->
  FCLOSED xs
->
  FCLOSED (FLet v e2 :: xs)
| fclosed_plus1 e2 xs:
  EXPCLOSED e2 ->
  FCLOSED xs
->
  FCLOSED (FPlus1 e2 :: xs)
| fclosed_plus2 v1 p xs:
  VALCLOSED v1 ->
  FCLOSED xs
->
  FCLOSED (FPlus2 v1 p :: xs)
| fclosed_if e2 e3 xs:
  EXPCLOSED e2 -> EXPCLOSED e3 ->
  FCLOSED xs
->
  FCLOSED (FIf e2 e3 :: xs).

Theorem Forall_implies_subscoped vl : forall vals Γ ξ,
  Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals
->
  subscoped vl Γ (ξ[[::= combine vl vals]]).
Proof.
  induction vl; intros.
  * apply eq_sym, length_zero_iff_nil in H0. subst. intro. intros. contradiction.
  * apply element_exist in H0 as H0'. destruct H0', H1. subst.
    intro. intros. cbn.
    inversion H0. inversion H. subst. pose (IHvl _ _ (ξ[[a ::= x]]) H6 H3).
    replace (fold_left (fun (ξ' : Substitution) '(x1, e) => ξ' [[x1 ::= e]]) (combine vl x0) (ξ [[a ::= x]])) with ((ξ [[a ::= x]])[[::= combine vl x0]]) by reflexivity. destruct (in_dec var_funid_eq_dec v vl).
    + apply s. auto.
    + erewrite subst_list_not_in; auto.  inversion H1. 2: contradiction. subst. inversion H. subst.
      unfold extend_subst. rewrite var_funid_eqb_refl. apply H7.
Qed.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FCLOSED F -> EXPCLOSED e
->
  FCLOSED F' /\ EXPCLOSED e'.
Proof.
  intros F e F' e' IH. induction IH; intros.
  * inversion H0. subst. inversion H4. subst. split; auto.
    constructor; auto. destruct v; inversion H; inversion H1; auto.
  * inversion H. inversion H0. subst. split; auto. inversion H5. exact H2.
  * inversion H. inversion H0. subst. split; auto. inversion H5. subst. cbn in H2.
    eapply subst_preserves_scope_rev; eauto. intro. intros. inversion H1. 2: contradiction.
    subst. unfold idsubst, extend_subst. rewrite var_funid_eqb_refl. auto.
  * inversion H0. subst. inversion H8. subst. split; auto. constructor; auto.
    apply Forall_app. split; auto. constructor; auto. destruct v'; inversion H'; inversion H1; auto.
  * inversion H3. subst. split; auto. inversion H9. eapply subst_preserves_scope_rev; eauto.
    intro. intros. Search extend_subst_list. Search extend_subst.
Qed.


