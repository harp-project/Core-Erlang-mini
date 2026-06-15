(**

  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we define the static semantics of Core Erlang
  expressions. We also connect these concepts to substitutions.
  This work is based on the techniques of Wand et al. [1].

  1: https://dl.acm.org/doi/10.1145/3236782

  We also introduce the syntax and static semantics for frames here
  which will be used by the frame stack semantics in `SubstSemantics.v`.
*)

Require Export ExpManipulation.
Export Relations.Relations.
Export Classes.RelationClasses.

Import ListNotations.

Reserved Notation "'EXP' Γ ⊢ e"
         (at level 69, no associativity).
Reserved Notation "'VAL' Γ ⊢ v"
         (at level 69, no associativity).
Reserved Notation "'NVAL' Γ ⊢ v"
         (at level 69, no associativity).
Inductive ExpScoped (Γ : nat) : Exp -> Prop :=
| scoped_val v :
  VAL Γ ⊢ v -> EXP Γ ⊢ v
| scoped_nonval e :
  NVAL Γ ⊢ e -> EXP Γ ⊢ e
with NonValScoped (Γ : nat) : NonVal -> Prop :=
| scoped_app exp (exps : list Exp) : 
  EXP Γ ⊢ exp ->
  (forall i, i < length exps -> EXP Γ ⊢ nth i exps (VLit 0%Z))
->
  NVAL Γ ⊢ EApp exp exps
| scoped_let e1 e2 :
  EXP Γ ⊢ e1 -> EXP (S Γ) ⊢ e2 
->
  NVAL Γ ⊢ ELet e1 e2
| scoped_case e1 e2 e3 p :
  EXP Γ ⊢ e1 -> EXP pat_vars p + Γ ⊢ e2 -> EXP Γ ⊢ e3
->
  NVAL Γ ⊢ ECase e1 p e2 e3
| escoped_cons e1 e2 :
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2
->
  NVAL Γ ⊢ ECons e1 e2
| scoped_conc_bif exp (exps : list Exp) : 
  EXP Γ ⊢ exp ->
  (forall i, i < length exps -> EXP Γ ⊢ nth i exps (VLit 0%Z))
->
  NVAL Γ ⊢ EBIF exp exps
| scoped_receive (l : list (Pat * Exp)) :
  (forall i, i < length l -> EXP (nth i (map (fst >>> pat_vars) l) 0) + Γ ⊢ nth i (map snd l) (VLit 0%Z))
->
  NVAL Γ ⊢ EReceive l

with ValScoped (Γ : nat) : Val -> Prop :=
| scoped_lit lit : VAL Γ ⊢ VLit lit
| scoped_pid p : VAL Γ ⊢ VPid p
| vscoped_cons e1 e2 : 
  VAL Γ ⊢ e1 -> VAL Γ ⊢ e2
->
  VAL Γ ⊢ VCons e1 e2
| scoped_nil : VAL Γ ⊢ VNil
| scoped_var n : n < Γ -> VAL Γ ⊢ VVar n
| scoped_fun vl e : EXP (S vl + Γ) ⊢ e -> VAL Γ ⊢ VFun vl e
where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)
and "'VAL' Γ ⊢ e" := (ValScoped Γ e)
and "'NVAL' Γ ⊢ e" := (NonValScoped Γ e).

Notation "'EXPCLOSED' e" := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v" := (VAL 0 ⊢ v) (at level 5).
Notation "'NVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5).

Global Hint Constructors ExpScoped : core.
Global Hint Constructors ValScoped : core.
Global Hint Constructors NonValScoped : core.

Scheme ExpScoped_ind2 := Induction for ExpScoped Sort Prop
  with NonValScoped_ind2 := Induction for NonValScoped Sort Prop
  with ValScoped_ind2 := Induction for ValScoped Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2, NonValScoped_ind2, ValScoped_ind2.

Definition subst_preserves (Γ : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> ξ v = inr v.

Theorem subst_preserves_up : forall Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (S Γ) (up_subst ξ).
Proof.
  intros. unfold subst_preserves in *. intros. unfold up_subst. destruct v; auto.
  unfold shift. rewrite H. reflexivity. lia.
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

Theorem scoped_ignores_sub_helper (exps : list Exp) : forall l ξ,
  (forall i : nat,
     i < Datatypes.length exps ->
     forall ξ : Substitution,
     subst_preserves l ξ -> subst ξ (nth i exps (VLit 0%Z)) = nth i exps (VLit 0%Z)) ->
  subst_preserves l ξ ->
  (map (subst ξ) exps) = exps.
Proof.
  induction exps; intros.
  * reflexivity.
  * simpl. epose (H 0 _ _ H0). simpl in e. rewrite e.
    erewrite IHexps; eauto. intros. eapply (H (S i)). simpl. lia. auto.
Unshelve. simpl. lia.
Qed.

Theorem Private_scoped_ignores_sub : forall Γ,
  (forall e, EXP Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ] = e) /\
  (forall e, NVAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.ₙ[ξ] = e) /\
  (forall e, VAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.ᵥ[ξ] = e)
  .
Proof.
  apply scoped_ind; intros; auto.
  * simpl. by rewrite H.
  * simpl. by rewrite H.
  * simpl. rewrite H; auto. erewrite scoped_ignores_sub_helper; eauto.
  * simpl. rewrite H; auto. rewrite H0; auto.
  * simpl. rewrite H, H0, H1; auto.
  * simpl. rewrite H, H0; auto.
  * simpl. rewrite H; auto. erewrite scoped_ignores_sub_helper; eauto.
  * simpl. induction l; auto. simpl. destruct a.
    epose proof (IHl _ _). inversion H1. repeat rewrite H3.
    epose proof (H 0 ltac:(simpl;lia) (upn (pat_vars p) ξ) _). simpl in H2. rewrite H2. reflexivity.
    Unshelve.
    intros. apply (e (S i)). simpl. lia.
    intros. apply (H (S i)). simpl. lia. simpl. auto.
    now apply subst_preserves_upn.
  * cbn. rewrite H, H0; auto.
  * specialize (H n l). simpl. rewrite H. auto.
  * simpl. epose (H _ _). rewrite e1. reflexivity.
    Unshelve. apply subst_preserves_up, subst_preserves_upn. auto.
Qed.

Corollary closed_ignores_sub :
  forall e ξ,
  EXPCLOSED e -> subst ξ e = e.
Proof.
  intros. eapply Private_scoped_ignores_sub with (Γ := 0); auto.
Qed.

Corollary closed_ignores_sub_val :
  forall e ξ,
  VALCLOSED e -> subst_val ξ e = e.
Proof.
  intros. pose proof (Private_scoped_ignores_sub 0) as [_ [_ ?]]. apply H0; auto.
Qed.

Corollary closed_ignores_sub_nonval :
  forall e ξ,
  NVALCLOSED e -> subst_nonval ξ e = e.
Proof.
  intros. pose proof (Private_scoped_ignores_sub 0) as [_ [? _]]. apply H0; auto.
Qed.

Global Hint Resolve closed_ignores_sub : core.

Global Hint Resolve closed_ignores_sub_val : core.

Global Hint Resolve closed_ignores_sub_nonval : core.

Theorem Private_scope_ext : forall Γ,
  (forall e, EXP Γ ⊢ e -> EXP (S Γ) ⊢ e) /\
  (forall e, NVAL Γ ⊢ e ->  NVAL (S Γ) ⊢ e) /\
  (forall e, VAL Γ ⊢ e ->  VAL (S Γ) ⊢ e).
Proof.
  apply scoped_ind; intros; constructor; try constructor 2; auto.
  * now replace (pat_vars p + S Γ) with (S (pat_vars p + Γ)) by lia.
  * intros. rewrite Nat.add_succ_r. auto.
  * rewrite Nat.add_succ_r; auto.
Qed.

Corollary scope_ext : forall {e Γ},
    EXP Γ ⊢ e -> EXP S Γ ⊢ e.
Proof.
  intros.
  apply Private_scope_ext.
  auto.
Qed.

Corollary scope_ext_val : forall {e Γ},
    VAL Γ ⊢ e -> VAL S Γ ⊢ e.
Proof.
  intros.
  apply Private_scope_ext.
  auto.
Qed.

Corollary scope_ext_nonval : forall {e Γ},
    NVAL Γ ⊢ e -> NVAL S Γ ⊢ e.
Proof.
  intros.
  apply Private_scope_ext.
  auto.
Qed.

Corollary Private_scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e) /\
  (forall e, NVAL Γ ⊢ e -> NVAL Γ' ⊢ e) /\
  (forall e, VAL Γ ⊢ e -> VAL Γ' ⊢ e).
Proof.
 intros. induction H.
 * intuition.
 * repeat split; intros; eapply Private_scope_ext; eapply IHle; auto. 
Qed.

Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e).
Proof. by apply Private_scope_ext_app. Qed.

Corollary scope_ext_app_val : forall Γ' Γ, Γ <= Γ' ->
  (forall e, VAL Γ ⊢ e -> VAL Γ' ⊢ e).
Proof. by apply Private_scope_ext_app. Qed.

Corollary scope_ext_app_nonval : forall Γ' Γ, Γ <= Γ' ->
  (forall e, NVAL Γ ⊢ e -> NVAL Γ' ⊢ e).
Proof. by apply Private_scope_ext_app. Qed.

Definition subscoped (Γ Γ' : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> (match ξ v with
                      | inl exp => VAL Γ' ⊢ exp
                      | inr num => num < Γ'  (** in case of identity subst *)
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

Lemma Private_ren_preserves_scope :
    (forall e Γ, EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (forall e Γ, NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ rename_nonval ξ e) /\
    (forall e Γ, VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename_val ξ e).
Proof.
  apply Exp_full_ind with
  (Q := Forall (fun e => forall Γ,(EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e)))
  (W := Forall (fun '(_,e) => forall Γ,(EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e))).
  15-18: by constructor.
  all: intros; split; intros; cbn; unfold renscoped in *.
  (* prove backward directions: *)
  all: try by (pose proof (H Γ) id (renscope_id _) as X ||
              pose proof (H0 Γ) id (renscope_id _) as X ||
              pose proof (H1 Γ) id (renscope_id _) as X ||
              pose proof (H2 Γ) id (renscope_id _) as X);
            (rewrite idrenaming_is_id in X ||
             rewrite idrenaming_is_id_val in X ||
             rewrite idrenaming_is_id_nonval in X);
           apply X.
  all: try by constructor.
  * inv H0. eapply H in H3; try eassumption. by constructor.
  * inv H0. eapply H in H3; try eassumption. by constructor.
  * constructor. apply H0. inversion H. auto.
  * constructor. inv H0. subst.
    eapply H; eauto. intros. pose proof (uprenn_scope (S  vl) _ Γ' ξ H1 v H0). auto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - intros. rewrite indexed_to_forall in H0.
      replace (˝VLit 0%Z) with (rename ξ (˝VLit 0%Z)) by auto.
      rewrite map_nth. rewrite length_map in H1. eapply H0; by eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; eauto. intros. eapply upren_scope; eauto.
  * inv H2. constructor.
    - eapply H; by eauto.
    - eapply H0; eauto. intros. eapply uprenn_scope; eauto.
    - eapply H1; by eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; by eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; by eauto.
  * inv H1. constructor.
    - eapply H; eauto.
    - intros. rewrite indexed_to_forall in H0.
      replace (˝VLit 0%Z) with (rename ξ (˝VLit 0%Z)) by auto.
      rewrite map_nth. rewrite length_map in H1. eapply H0; eauto.
  * inv H0. constructor. intros. rewrite length_map in H0. generalize dependent i.
    induction l; intros.
    - inv H0.
    - destruct i; simpl.
      + destruct a; cbn.
        specialize (H3 0 ltac:(lia)). cbn in H3.
        inv H. eapply H5; try eassumption.
        by eapply uprenn_scope.
      + simpl in H1. eapply IHl; auto.
        now inversion H. 2: simpl in H0; lia.
        intros. apply (H3 (S i0)). simpl. lia.
Qed.

Corollary ren_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply Private_ren_preserves_scope.
Qed.

Lemma ren_preserves_scope_val : forall e Γ,
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename_val ξ e).
Proof.
  intros.
  apply Private_ren_preserves_scope.
Qed.

Lemma ren_preserves_scope_nonval : forall e Γ,
    (NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ rename_nonval ξ e).
Proof.
  intros.
  apply Private_ren_preserves_scope.
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

Lemma consn_scope : forall (vals : list Val) Γ Γ' (ξ : Substitution),
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
Lemma Private_subst_preserves_scope :
    (forall e Γ, EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
    (forall e Γ, NVAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ e.ₙ[ξ]) /\
    (forall e Γ, VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.ᵥ[ξ]).
Proof.
  apply Exp_full_ind with
  (Q :=
  Forall (fun e => forall Γ, (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ])))
  (W :=
  Forall (fun '(_,e) => forall Γ, (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ])));
    try intros;
    try split;
    try split;
    intros.
  all: cbn; unfold subscoped in *.
  (* prove backward directions: *)
  all: try by ((specialize (H0 Γ idsubst (scope_idsubst _)) as X ||
                specialize (H Γ idsubst (scope_idsubst _)) as X ||
                specialize (H2 Γ idsubst (scope_idsubst _)) as X ||
                specialize (H1 Γ idsubst (scope_idsubst _)) as X);
             (rewrite idsubst_is_id in X ||
              rewrite idsubst_is_id_val in X ||
              rewrite idsubst_is_id_nonval in X); apply X).

  15-18: by constructor.
  (* forward: *)
  * inv H0. constructor. by eapply H.
  * inv H0. constructor. by eapply H.
  * constructor.
  * constructor.
  * inv H. specialize (H0 n H2). break_match_goal. by simpl. by constructor.
  * constructor. inv H0. eapply H; eauto. intros.
    eapply up_scope; eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - replace (˝VLit 0%Z) with (subst ξ (˝VLit 0%Z)) by reflexivity. intros.
      specialize (H6 i).
      rewrite map_nth. rewrite indexed_to_forall in H0. rewrite length_map in H1.
      eapply H0; by eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; eauto. apply up_scope. by auto.
  * inv H2. constructor.
    - eapply H; eauto.
    - eapply H0; eauto. apply upn_scope. auto.
    - eapply H1; eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; by eauto.
  * by constructor.
  * inv H1. constructor.
    - eapply H; by eauto.
    - eapply H0; by eauto.
  * inv H1. constructor.
    - eapply H; by eauto.
    - replace (˝VLit 0%Z) with (subst ξ (˝VLit 0%Z)) by reflexivity. intros.
      specialize (H6 i).
      rewrite map_nth. rewrite indexed_to_forall in H0. rewrite length_map in H1.
      eapply H0; by eauto.
  * inv H0. constructor.
    intros. rewrite length_map in H0. generalize dependent i. induction l; intros.
    - inversion H0.
    - destruct i; simpl.
      + destruct a; cbn. inversion H. subst.
        eapply H5; eauto. apply (H3 0). simpl. lia. apply upn_scope; auto.
      + inv H. simpl in H0. eapply IHl; eauto. 2: lia.
        intros. apply (H3 (S i0)). simpl. lia.
Qed.

Corollary subst_preserves_scope_exp : forall e Γ,
    EXP Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      EXP Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply Private_subst_preserves_scope.
Qed.

Corollary subst_preserves_scope_nonval : forall e Γ,
    NVAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      NVAL Γ' ⊢ e.ₙ[ξ].
Proof.
  intros.
  apply Private_subst_preserves_scope.
Qed.

Corollary subst_preserves_scope_val : forall e Γ,
    VAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      VAL Γ' ⊢ e.ᵥ[ξ].
Proof.
  intros.
  apply Private_subst_preserves_scope.
Qed.

Module SUB_IMPLIES_SCOPE.
  Definition magic_ξ (Γ Γ' : nat) (n : nat) : Val + nat :=
    if Compare_dec.lt_dec n Γ
    then if Compare_dec.lt_dec n Γ'
         then inr n
         else inl (VLit 0%Z)
    else inr Γ'.

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

  Lemma Private_magic_ξ_implies_scope :
      (forall e Γ Γ', EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (forall e Γ Γ', NVAL Γ' ⊢ e.ₙ[magic_ξ Γ Γ'] ->
       NVAL Γ ⊢ e) /\
      (forall e Γ Γ', VAL Γ' ⊢ e.ᵥ[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e).
  Proof.
    apply Exp_full_ind with
    (Q := Forall (fun e => forall Γ Γ', (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e)))
    (W := Forall (fun '(_,e) => forall Γ Γ', (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e))); intros.
    15-18: by constructor.
    all: cbn in *.
    all: try match goal with
    | [H : EXP _ ⊢ _ |- _] => inv H
    | [H : NVAL _ ⊢ _ |- _] => inv H
    (* | [H : VAL _ ⊢ _ |- _] => inv H *)
    end.
    3-4, 11: by constructor. (* lit, nil, pid *)
    all: try (constructor; try eapply H; try eapply H0; try eapply H1; by eassumption).
    * break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inv H. lia.
    * constructor. inv H0.
      eapply H. replace (up_subst (upn vl (magic_ξ Γ Γ'))) with
                          (upn (S vl) ((magic_ξ Γ Γ'))) in H2 by reflexivity.
      rewrite upn_magic in H2. eauto.
    * constructor.
      - eapply H; eauto.
      - replace (˝VLit 0%Z) with (subst (magic_ξ Γ Γ') (˝VLit 0%Z)) in H5 by reflexivity.
        intros. rewrite length_map in H5. specialize (H5 i H1).
        rewrite map_nth in H5. subst. rewrite indexed_to_forall in H0.
        eapply H0; eauto.
    * constructor.
      - eapply H; eauto.
      - eapply H0; eauto. rewrite up_magic in H5. eauto.
    * constructor.
      - eapply H; eauto.
      - eapply H0; eauto.
        rewrite upn_magic in H8. exact H8.
      - eapply H1; eauto.
    * inv H1. constructor.
      + eapply H; eauto.
      + eapply H0; eauto.
    * constructor.
      - eapply H; eauto.
      - replace (˝VLit 0%Z) with (subst (magic_ξ Γ Γ') (˝VLit 0%Z)) in H5 by reflexivity.
        intros. rewrite length_map in H5. specialize (H5 i H1).
        rewrite map_nth in H5. subst. rewrite indexed_to_forall in H0.
        eapply H0; eauto.
    * constructor. induction l; intros.
        + inversion H0.
        + destruct i.
          ** simpl. destruct a. inversion H. subst. cbn. eapply H4.
             specialize (H2 0 ltac:(simpl;lia)). cbn in H2.
             rewrite upn_magic in H2. exact H2.
          ** simpl. inversion H. subst. apply IHl; auto.
             intros. apply (H2 (S i0)). simpl. lia.
             simpl in H0. lia.
  Qed.

  Lemma sub_implies_scope_exp : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ e.[ξ]) ->
      EXP Γ ⊢ e.
  Proof.
    intros;
    eapply Private_magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Lemma sub_implies_scope_nonval : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> NVAL Γ' ⊢ e.ₙ[ξ]) ->
      NVAL Γ ⊢ e.
  Proof.
    intros;
    eapply Private_magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ e.ᵥ[ξ]) ->
      VAL Γ ⊢ e.
  Proof.
    intros;
    eapply Private_magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Definition magic_ξ_2 Γ' :=
    fun n =>
      if Compare_dec.lt_dec n Γ'
      then idsubst n
      else if Nat.eq_dec n Γ'
           then inl (VLit 0%Z)
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

  Lemma magic_const : magic_ξ_2 0 = VLit 0%Z .: idsubst.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst. inversion l.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto. lia.
  Qed.

  Lemma magic_ξ_magic_ξ_2 :
      (forall e Γ', EXP Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
      (forall e Γ', NVAL Γ' ⊢ e.ₙ[magic_ξ_2 Γ'] ->
       e.ₙ[magic_ξ (S Γ') Γ'] = e.ₙ[magic_ξ_2 Γ']) /\
      (forall e Γ', VAL Γ' ⊢ e.ᵥ[magic_ξ_2 Γ'] ->
       e.ᵥ[magic_ξ (S Γ') Γ'] = e.ᵥ[magic_ξ_2 Γ']).
  Proof.
    apply Exp_full_ind with
      (Q := Forall (fun e => forall Γ',
        (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ'])
      ))
      (W := Forall (fun '(_,e) => forall Γ',
        (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ'])
      )); intros; cbn; auto.
    all: try match goal with
    | [H : EXP _ ⊢ _ |- _] => inv H
    | [H : NVAL _ ⊢ _ |- _] => inv H
    (* | [H : VAL _ ⊢ _ |- _] => inv H *)
    end.
    all: try (try rewrite H; try assumption; try rewrite H0; try assumption;
          try rewrite H1; by reflexivity).
    * unfold magic_ξ_2, magic_ξ, idsubst.
      repeat destruct Compare_dec.lt_dec; try destruct Nat.eq_dec; auto.
      lia. lia. lia. cbn in H. unfold magic_ξ_2 in H.
      repeat case_match; try lia.
      - inv H0.
      - inv H0. inv H. lia.
    * inv H0. rewrite upn_magic, up_magic, upn_magic_2, up_magic_2.
      replace (S (vl + S Γ')) with (S (S vl + Γ')) by lia.
      specialize (H (S (vl + Γ'))).
      rewrite <- H; auto. by rewrite upn_magic_2, up_magic_2 in H2.
    * rewrite H. 2: assumption.
      erewrite map_ext_Forall. reflexivity.
      rewrite indexed_to_forall in *. intros. apply H0; auto.
      replace (˝VLit 0%Z) with ((˝VLit 0%Z).[magic_ξ_2 Γ']) in H5 by reflexivity.
      rewrite length_map in H5. specialize (H5 i H1). rewrite map_nth in H5.
      exact H5.
    * rewrite H. 2: assumption.
      rewrite up_magic, up_magic_2, H0; auto.
      now rewrite up_magic_2 in H5.
    * rewrite upn_magic, upn_magic_2.
      rewrite H. 2: assumption.
      rewrite H1. 2: assumption.
      specialize (H0 (pat_vars p + Γ')).
      rewrite <- plus_n_Sm.
      rewrite H0. reflexivity.
      by rewrite upn_magic_2 in H8.
    * inv H1.
      rewrite H. 2: assumption.
      by rewrite H0.
    * rewrite H. 2: assumption.
      erewrite map_ext_Forall. reflexivity.
      rewrite indexed_to_forall in *. intros. apply H0; auto.
      replace (˝VLit 0%Z) with ((˝VLit 0%Z).[magic_ξ_2 Γ']) in H5 by reflexivity.
      rewrite length_map in H5. specialize (H5 i H1). rewrite map_nth in H5.
      exact H5.
    * induction l; simpl; auto.
      intros. destruct a. inv H.
      epose proof (IH := IHl H4 _). inversion IH. rewrite H0.
      specialize (H3 (pat_vars p + Γ')).
      rewrite upn_magic, upn_magic_2. rewrite <- plus_n_Sm. rewrite H3. reflexivity.
      specialize (H2 0 ltac:(simpl;lia)).
      cbn in H2. rewrite upn_magic_2 in H2. auto.
  Unshelve. intros. apply (H2 (S i) ltac:(simpl; lia)).
  Qed.

  Lemma magic_ξ_magic_ξ_2_closed :
      (forall e, EXPCLOSED e.[VLit 0%Z/] ->
       e.[magic_ξ 1 0] = e.[VLit 0%Z .: idsubst]) /\
      (forall e, NVALCLOSED e.ₙ[VLit 0%Z/] ->
       e.ₙ[magic_ξ 1 0] = e.ₙ[VLit 0%Z .: idsubst]) /\
      (forall e, VALCLOSED e.ᵥ[VLit 0%Z/] ->
       e.ᵥ[magic_ξ 1 0] = e.ᵥ[VLit 0%Z .: idsubst]).
  Proof.
    intros.
    rewrite <- magic_const.
    repeat split; intros; eapply magic_ξ_magic_ξ_2; assumption.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e,
      EXPCLOSED e.[VLit 0%Z/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply Private_magic_ξ_implies_scope.
    rewrite (proj1 (magic_ξ_magic_ξ_2_closed)); assumption.
  Qed.

  Lemma sub_implies_scope_nonval_1 : forall e,
      NVALCLOSED e.ₙ[VLit 0%Z/] ->
      NVAL 1 ⊢ e.
  Proof.
    intros;
      eapply Private_magic_ξ_implies_scope.
    rewrite (proj1 (proj2 (magic_ξ_magic_ξ_2_closed))); assumption.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e,
      VALCLOSED e.ᵥ[VLit 0%Z/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply Private_magic_ξ_implies_scope.
    rewrite (proj2 (proj2 (magic_ξ_magic_ξ_2_closed))); assumption.
  Qed.

End SUB_IMPLIES_SCOPE.

Definition subst_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition subst_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition subst_implies_scope_nonval := SUB_IMPLIES_SCOPE.sub_implies_scope_nonval.
Definition subst_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition subst_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.
Definition subst_implies_scope_nonval_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_nonval_1.

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

Corollary upn_ignores_sub :
     (forall e Γ ξ, EXP Γ ⊢ e -> e.[upn Γ ξ] = e) /\
     (forall e Γ ξ, NVAL Γ ⊢ e -> e.ₙ[upn Γ ξ] = e) /\
     (forall e Γ ξ, VAL Γ ⊢ e -> e.ᵥ[upn Γ ξ] = e).
Proof.
  intros. repeat split; intros.
  * eapply Private_scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
  * eapply Private_scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
  * eapply Private_scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
Qed.

Lemma scoped_ignores_sub : forall e Γ ξ,
    EXP Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve scoped_ignores_sub : core.

Lemma scoped_ignores_sub_nonval : forall e Γ ξ,
    NVAL Γ ⊢ e -> e.ₙ[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve scoped_ignores_sub_nonval : core.

Lemma scoped_ignores_sub_val : forall e Γ ξ,
    VAL Γ ⊢ e -> e.ᵥ[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve scoped_ignores_sub_val : core.

Lemma closed_sub_closed : forall v ξ,
    EXPCLOSED v -> EXPCLOSED v.[ξ].
Proof.
  intros.
  rewrite closed_ignores_sub;
    auto.
Qed.
Global Hint Resolve closed_sub_closed : core.

Lemma closed_sub_closed_nonval : forall v ξ,
    NVALCLOSED v -> NVALCLOSED v.ₙ[ξ].
Proof.
  intros.
  rewrite closed_ignores_sub_nonval;
    auto.
Qed.
Global Hint Resolve closed_sub_closed_nonval : core.

Lemma closed_sub_closed_val : forall v ξ,
   VALCLOSED v -> VALCLOSED v.ᵥ[ξ].
Proof.
  intros.
  rewrite closed_ignores_sub_val;
    auto.
Qed.
Global Hint Resolve closed_sub_closed_val : core.

(** FrameStack *)
(** Based on Pitts' work (https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf) *)
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Val) (l1 : list Val) (l2 : list Exp) (* apply v(v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ) *)
| FLet (e2 : Exp) (* let v = □ in e2 *)
| FCase (p : Pat) (e2 e3 : Exp) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (* [e1 | □] *)
| FCons2 (v2 : Val) (* [□ | v2] *)
| FBIF1 (l : list Exp) (* call □(e₁, e₂, ..., eₙ) *)
| FBIF2 (v : Val) (l1 : list Val) (l2 : list Exp) (* call v(v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ) *).

(* Inductive frame_wf : Frame -> Prop :=
| wf_app1 l : frame_wf (FApp1 l)
| wf_app2 vl b l1 l2 :  Forall (fun v => VALCLOSED v) l2 -> frame_wf (FApp2 (EFun vl b) l1 l2)
| wf_let v e : frame_wf (FLet v e)
| wf_if p e2 e3 : frame_wf (FCase p e2 e3)
| wf_cons1 e : frame_wf (FCons1 e)
| wf_cons2 v : VALCLOSED v -> frame_wf (FCons2 v)
| wf_bif1 l : frame_wf (FBIF1 l)
| wf_bif2 vl b l1 l2 :  Forall (fun v => VALCLOSED v) l2 -> frame_wf (FBIF2 (EFun vl b) l1 l2). *)

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FApp1 l => EApp e l
 | FApp2 v l1 l2 => EApp v (map VVal l1 ++ [e] ++ l2)
 | FLet e2 => ELet e e2
 | FCase p e2 e3 => ECase e p e2 e3
 | FCons1 e1 => ECons e1 e
 | FCons2 v2 => ECons e v2
 | FBIF1 l => EBIF e l
 | FBIF2 v l1 l2 => EBIF v (map VVal l1 ++ [e] ++ l2)
end.

Definition FrameStack := list Frame.

Inductive FCLOSED : Frame -> Prop :=
| fclosed_app1 l:
  Forall (fun e => EXPCLOSED e) l
->
  FCLOSED (FApp1 l)
| fclosed_app2 v l1 l2:
  VALCLOSED v -> Forall (fun e => VALCLOSED e) l1 -> Forall (fun e => EXPCLOSED e) l2
->
  FCLOSED (FApp2 v l1 l2)
| fclosed_let e2 :
  EXP 1 ⊢ e2
->
  FCLOSED (FLet e2)
| fclosed_if e2 e3 p:
  EXP pat_vars p ⊢ e2 -> EXPCLOSED e3
->
  FCLOSED (FCase p e2 e3)
| fclosed_cons1 e1:
  EXPCLOSED e1
->
  FCLOSED (FCons1 e1)
| fclosed_cons2 v:
  VALCLOSED v
->
  FCLOSED (FCons2 v)
| fclosed_bif1 l:
  Forall (fun e => EXPCLOSED e) l
->
  FCLOSED (FBIF1 l)
| fclosed_bif2 v l1 l2:
  VALCLOSED v -> Forall (fun e => VALCLOSED e) l1 -> Forall (fun e => EXPCLOSED e) l2
->
  FCLOSED (FBIF2 v l1 l2).

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

Lemma substcomp_scoped :
  forall ξ σ Γ Δ Ω, SUBSCOPE Γ ⊢ ξ ∷ Δ -> SUBSCOPE Δ ⊢ σ ∷ Ω
->
  SUBSCOPE Γ ⊢ ξ >> σ ∷ Ω.
Proof.
  intros. intro. intros. unfold subscoped in H.
  unfold ">>".
  specialize (H v H1).
  destruct (ξ v) eqn:D1.
  * apply -> subst_preserves_scope_val; eassumption.
  * specialize (H0 n H). auto.
Qed.

Theorem match_pattern_scoped : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Some l
->
  Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p; intros.
  * simpl in *. destruct v; inversion H0. break_match_hyp; inversion H0. auto.
  * simpl in *. destruct v; inversion H0. break_match_hyp; inversion H0. auto.
  * simpl in *. destruct v; inversion H0; subst; auto.
  * simpl in *. destruct v; inversion H0. subst. auto.
  * simpl. simpl in H0. destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion H0.
    subst. apply Forall_app. split.
    - inversion H. subst. eapply IHp1. exact H3. auto.
    - inversion H. subst. eapply IHp2. exact H4. auto.
Qed.

(* Theorem scoped_dec : 
  forall e Γ, (EXP Γ ⊢ e \/ ~ EXP Γ ⊢ e) /\ (VAL Γ ⊢ e \/ ~ VAL Γ ⊢ e).
Proof.
  induction e using Exp_ind2 with
    (Q := fun l => Forall (fun e => forall Γ, (EXP Γ ⊢ e \/ ~ EXP Γ ⊢ e) /\ (VAL Γ ⊢ e \/ ~ VAL Γ ⊢ e)) l)
    (W := fun l => Forall (fun '(_,e) => forall Γ, (EXP Γ ⊢ e \/ ~ EXP Γ ⊢ e) /\ (VAL Γ ⊢ e \/ ~ VAL Γ ⊢ e)) l); intros.
  * split; left; constructor; constructor.
  * split; left; constructor; constructor.
  * destruct (Compare_dec.lt_dec n Γ).
    - split; left; constructor; auto. constructor. auto.
    - split; right; intro; inversion H; inversion H0; congruence.
  * destruct (Compare_dec.lt_dec n Γ).
    - split; left; constructor; auto. constructor. auto.
    - split; right; intro; inversion H; inversion H0; congruence.
  * destruct (IHe (S (length vl) + Γ)) as [[H0_1 | H0_2] H1].
    - split; left. now do 2 constructor. now constructor.
    - split; right; intro; inversion H; inversion H0; subst; congruence.
  * destruct (IHe Γ) as [[P1 | P2] ?].
    - induction el; cbn.
      + split. left. constructor; auto. intros. inversion H0.
        right; intro; inversion H0.
      + inversion IHe0. subst. clear IHe0. destruct (H2 Γ).
        apply IHel in H3 as [P1' P2']. inversion P1'.
        ** inversion H3. 2: inversion_is_value. subst. split.
           -- inversion H0.
              ++ left. constructor; auto. intros. destruct i; auto.
                 cbn. apply H7. simpl in H5. lia.
              ++ right. intro. inversion H5. 2: inversion_is_value.
                 specialize (H11 0 ltac:(simpl;lia)).
                 subst. simpl in H11. congruence.
           -- right. intro. inversion_is_value.
        ** split.
           -- right. intro.
              assert (EXP Γ ⊢ EApp e el).
              { constructor; auto. inversion H4. 2: inversion_is_value.
                intros. apply (H8 (S i)). simpl. lia. }
              congruence.
           -- right. intro. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * destruct (IHe1 Γ) as [[P1 | P2] ?].
    - destruct (IHe2 (S Γ)) as [[P1' | P2'] ?].
      + split. left. constructor; auto. right. intro. inversion_is_value.
      + split; right; intro; inversion H1. congruence. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * destruct (IHe1 (S (length vl) + Γ)) as [[P1 | P2] ?].
    - destruct (IHe2 (S Γ)) as [[P1' | P2'] ?].
      + split. left. constructor; auto. right. intro. inversion_is_value.
      + split; right; intro; inversion H1. congruence. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * destruct (IHe1 Γ) as [[P1 | P2] ?].
    - destruct (IHe2 (pat_vars p + Γ)) as [[P1' | P2'] ?].
      + destruct (IHe3 Γ) as [[P1'' | P2''] ?].
        ** split. left. constructor; auto. right. intro. inversion_is_value.
        ** split; right; intro; inversion H2. congruence. inversion_is_value.
      + split; right; intro; inversion H1. congruence. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * destruct (IHe1 Γ) as [[P1 | P2] ?].
    - destruct (IHe2 Γ) as [[P1' | P2'] ?].
      + split. left. constructor; auto. right. intro. inversion_is_value.
      + split; right; intro; inversion H1. congruence. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * split; left; constructor; constructor.
  * destruct (IHe1 Γ) as [? [P1 | P2]].
    - destruct (IHe2 Γ) as [? [P1' | P2']].
      + split. left. do 2 constructor; auto. left; now constructor.
      + split; right; intro; inversion H1; inversion H2; congruence.
    - split; right; intro; inversion H0; inversion H1; congruence.
  * destruct (IHe Γ) as [[P1 | P2] ?].
    - induction l; cbn.
      + split. left. constructor; auto. intros. inversion H0.
        right; intro; inversion H0.
      + inversion IHe0. subst. clear IHe0. destruct (H2 Γ).
        apply IHl in H3 as [P1' P2']. inversion P1'.
        ** inversion H3. 2: inversion_is_value. subst. split.
           -- inversion H0.
              ++ left. constructor; auto. intros. destruct i; auto.
                 cbn. apply H7. simpl in H5. lia.
              ++ right. intro. inversion H5. 2: inversion_is_value.
                 specialize (H11 0 ltac:(simpl;lia)).
                 subst. simpl in H11. congruence.
           -- right. intro. inversion_is_value.
        ** split.
           -- right. intro.
              assert (EXP Γ ⊢ EBIF e l).
              { constructor; auto. inversion H4. 2: inversion_is_value.
                intros. apply (H8 (S i)). simpl. lia. }
              congruence.
           -- right. intro. inversion_is_value.
    - split; right; intro; inversion H0. congruence. inversion_is_value.
  * induction l.
    - split. left. constructor. intros. inversion H. right. intro. inversion H.
    - inversion IHe. subst. destruct a. destruct (H1 (pat_vars p + Γ)) as [E V].
      destruct E.
      + apply IHl in H2 as [E2 V2]. destruct E2.
        ** split. left. constructor. intros. destruct i.
           exact H.
           cbn in *. inversion H0. 2: inversion H3. subst. apply (H4 i). lia.
           right. intro. inversion H2.
        ** split; right; intro; inversion H2. 2: inversion H3.
           assert (EXP Γ ⊢ EReceive l). { constructor. intros. apply (H4 (S i)). simpl. lia. }
           congruence.
      + split; right; intro; inversion H0. 2: inversion H3. subst.
        specialize (H4 0 ltac:(simpl;lia)). cbn in H4. congruence.
  * constructor.
  * constructor; auto.
  * constructor.
  * constructor; auto.
Qed.

Corollary valscoped_dec Γ : 
  forall e, VAL Γ ⊢ e \/ ~ VAL Γ ⊢ e.
Proof.
  intros. apply scoped_dec.
Qed.

Corollary expscoped_dec Γ : 
  forall e, EXP Γ ⊢ e \/ ~ EXP Γ ⊢ e.
Proof.
  intros. apply scoped_dec.
Qed. *)

