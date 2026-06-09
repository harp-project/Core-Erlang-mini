(**
  Static semantics (scoping) for the environment-based Core Erlang syntax.

  Analogous to src/Scoping.v for the substitution-based syntax.

  The key differences from the substitution-based scoping:

  - [VVar n] is a value that looks up index [n] in the runtime environment,
    so it is well-scoped when [n < Γ].

  - [EFun vl e] is a NonVal constructor (not yet a value).  Before the
    closure is formed its body [e] may still refer to the surrounding
    environment, so the body must be scoped in [S vl + Γ]
    (0 = self, 1..vl = params, S vl .. S vl + Γ - 1 = outer env).

  - [VClos Γ_env vl e] is a runtime closure that has already captured its
    environment.  The values stored in [Γ_env] must be scoped in the outer
    context [Γ], and the body [e] must be scoped in [S vl + length Γ_env]
    (self + params + captured-env slots).

  - Frames each store a saved environment [Γ_saved : list Val].  A frame is
    "closed" when [Γ_saved] is a well-formed environment and the
    sub-expressions/values inside the frame are scoped appropriately with
    respect to [Γ_saved].
*)

From CoreErlang.Env Require Export Semantics.
Import ListNotations.
Open Scope env_scope.

(** * Scoping judgements for expressions, non-values, and values *)


(* Vals are closed, other stuff are scoped
   Issue: Different signatures
   Solutions:
     - parametric val closedness relation
     - constant 0 parameter for value scoping
     - separate inductive type which defines the signature
       for the scoping type
 *)

Module parametric.

Inductive scoped_exp (Γ : nat) (valscope : Val -> Prop) : Exp -> Prop :=

with scoped_nonval (Γ : nat) (valscope : Val -> Prop) : NonVal -> Prop :=

.


(* This is not this simple: *)

Fail Inductive closed_val : Val -> Prop :=

| scoped_clos Γ vl e :
  scoped_exp (length Γ) closed_val e ->
  closed_val (VClos Γ vl e)
.

End parametric.

Module constant0.

(* This works: *)
Inductive scoped_exp : nat -> Exp -> Prop :=

with scoped_nonval : nat -> NonVal -> Prop :=

with closed_val : nat -> Val -> Prop :=

| scoped_clos Γ vl e :
  scoped_exp (length Γ) e ->
  closed_val 0 (VClos Γ vl e)
.


End constant0.

Module twolevel.

(* This works too: *)

Inductive typing :=
| scoped_exp (n : nat) (e : Exp)
| scoped_nonval (n : nat) (n : NonVal)
| closed_val (v : Val).

Inductive scoping : typing -> Prop :=

| scoped_clos Γ vl e :
  scoping (scoped_exp (length Γ) e) ->
  scoping (closed_val (VClos Γ vl e))
.

End twolevel.


Reserved Notation "'EXP' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'NVAL' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'VAL' Γ ⊢ v" (at level 69, no associativity).

Inductive ExpScoped (Γ : nat) : Exp -> Prop :=
| scoped_val v :
  VAL Γ ⊢ v ->
  EXP Γ ⊢ (VVal v)
| scoped_nonval nv :
  NVAL Γ ⊢ nv ->
  EXP Γ ⊢ (EExp nv)

with NonValScoped (Γ : nat) : NonVal -> Prop :=
| scoped_fun vl e :
  (** Before capture: body sees self + params on top of the outer env. *)
  EXP (S vl + Γ) ⊢ e ->
  NVAL Γ ⊢ EFun vl e
| scoped_app exp exps :
  EXP Γ ⊢ exp ->
  (forall i, i < length exps -> EXP Γ ⊢ nth i exps (˝VLit 0%Z)) ->
  NVAL Γ ⊢ EApp exp exps
| scoped_let e1 e2 :
  EXP Γ ⊢ e1 ->
  EXP (S Γ) ⊢ e2 ->
  NVAL Γ ⊢ ELet e1 e2
| scoped_case e p e1 e2 :
  EXP Γ ⊢ e ->
  EXP (pat_vars p + Γ) ⊢ e1 ->
  EXP Γ ⊢ e2 ->
  NVAL Γ ⊢ ECase e p e1 e2
| scoped_cons e1 e2 :
  EXP Γ ⊢ e1 ->
  EXP Γ ⊢ e2 ->
  NVAL Γ ⊢ ECons e1 e2
| scoped_bif exp exps :
  EXP Γ ⊢ exp ->
  (forall i, i < length exps -> EXP Γ ⊢ nth i exps (˝VLit 0%Z)) ->
  NVAL Γ ⊢ EBIF exp exps
| scoped_var n   : n < Γ -> NVAL Γ ⊢ EVar n


with ValScoped (Γ : nat) : Val -> Prop :=
| scoped_lit l   : VAL Γ ⊢ VLit l
| scoped_pid p   : VAL Γ ⊢ VPid p
| scoped_nil     : VAL Γ ⊢ VNil
| scoped_cons_v v1 v2 :
  VAL Γ ⊢ v1 ->
  VAL Γ ⊢ v2 ->
  VAL Γ ⊢ VCons v1 v2
| scoped_clos Γ_env vl e :
  (** Captured-environment values are scoped in the outer context [Γ]. *)
  (forall i, i < length Γ_env -> VAL Γ ⊢ nth i Γ_env (VLit 0%Z)) ->
  (** Body is scoped in self + params + captured-env. *)
  EXP (S vl + length Γ_env) ⊢ e ->
  VAL Γ ⊢ VClos Γ_env vl e

where "'EXP' Γ ⊢ e" := (ExpScoped Γ e) : env_scope
and   "'NVAL' Γ ⊢ e" := (NonValScoped Γ e) : env_scope
and   "'VAL' Γ ⊢ v"  := (ValScoped Γ v) : env_scope.

Notation "'EXPCLOSED' e"  := (EXP 0 ⊢ e)  (at level 5) : env_scope.
Notation "'VALCLOSED' v"  := (VAL 0 ⊢ v)  (at level 5) : env_scope.
Notation "'NVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5) : env_scope.

Global Hint Constructors ExpScoped  : core.
Global Hint Constructors NonValScoped : core.
Global Hint Constructors ValScoped  : core.

Scheme ExpScoped_ind2    := Induction for ExpScoped    Sort Prop
  with NonValScoped_ind2 := Induction for NonValScoped Sort Prop
  with ValScoped_ind2    := Induction for ValScoped    Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2, NonValScoped_ind2, ValScoped_ind2.

(** * Scope weakening (monotonicity) *)

(**
  Weakening: a term scoped in [Γ] is also scoped in any larger context.
  Stated here for a single successor; the general version follows by induction
  on [Γ' - Γ].

  Proof by [scoped_ind].  With [nth]-based indexing uniform across all list
  premises (including [scoped_clos]), [Scheme] now generates a matching IH
  for every premise, so the proof structure is the same as in [Scoping.v].

  Cases:

  - [scoped_val], [scoped_nonval]: IH from PV / PN.

  - [scoped_fun vl e]:
      Have [EXP (S vl + Γ) ⊢ e], need [EXP (S vl + S Γ) ⊢ e].
      Rewrite [S vl + S Γ = S (S vl + Γ)] by [lia]; apply the IH for [e].

  - [scoped_app exp exps], [scoped_bif exp exps]:
      IH for [exp].  For each argument: [scoped_ind] generates
      [forall i, i < length exps -> PV (nth i exps ...)] as IH;
      rewrite the length and apply it pointwise.

  - [scoped_let e1 e2]:
      IH for [e1].
      For [e2]: have [EXP (S Γ) ⊢ e2], need [EXP (S (S Γ)) ⊢ e2];
      IH applies at context size [S Γ] giving the result directly.

  - [scoped_case e p e1 e2]:
      IH for [e] and [e2].
      For [e1]: rewrite [pat_vars p + S Γ = S (pat_vars p + Γ)] by [lia];
      apply the IH for [e1].

  - [scoped_cons e1 e2]: IH on both subterms.

  - [scoped_lit], [scoped_pid], [scoped_nil]: trivial constructors.

  - [scoped_var n]: [n < Γ → n < S Γ] by [lia].

  - [scoped_cons_v v1 v2]: IH on both components.

  - [scoped_clos Γ_env vl e]:
      * Captured environment: have
          [forall i, i < length Γ_env -> VAL Γ ⊢ nth i Γ_env (VLit 0%Z)];
          [scoped_ind] generates IH
          [forall i, i < length Γ_env -> PV (nth i Γ_env (VLit 0%Z))],
          so we can conclude
          [forall i, i < length Γ_env -> VAL (S Γ) ⊢ nth i Γ_env (VLit 0%Z)]
          by applying the IH pointwise.
      * Body: [EXP (S vl + length Γ_env) ⊢ e] is independent of [Γ];
          reuse the hypothesis unchanged.

  The only nontrivial arithmetic rewrites are:
    [S vl + S Γ = S (S vl + Γ)]          (for [scoped_fun])
    [pat_vars p + S Γ = S (pat_vars p + Γ)]  (for [scoped_case])
  both discharged by [lia].
*)
Theorem Private_scope_ext : forall Γ,
  (forall e, EXP Γ ⊢ e  -> EXP  (S Γ) ⊢ e) /\
  (forall e, NVAL Γ ⊢ e -> NVAL (S Γ) ⊢ e) /\
  (forall v, VAL Γ ⊢ v  -> VAL  (S Γ) ⊢ v).
Proof.
  apply scoped_ind; intros; constructor; try constructor 2; auto.
  - (* scoped_fun: S vl + S Γ = S (S vl + Γ) *)
    now replace (S vl + S Γ) with (S (S vl + Γ)) by lia.
  - (* scoped_case, true branch: pat_vars p + S Γ = S (pat_vars p + Γ) *)
    now replace (pat_vars p + S Γ) with (S (pat_vars p + Γ)) by lia.
Qed.

Corollary scope_ext : forall {e Γ},
  EXP Γ ⊢ e -> EXP (S Γ) ⊢ e.
Proof. intros. exact (proj1 (Private_scope_ext Γ) e H). Qed.

Corollary scope_ext_val : forall {v Γ},
  VAL Γ ⊢ v -> VAL (S Γ) ⊢ v.
Proof. intros. exact (proj2 (proj2 (Private_scope_ext Γ)) v H). Qed.

Corollary scope_ext_nonval : forall {e Γ},
  NVAL Γ ⊢ e -> NVAL (S Γ) ⊢ e.
Proof. intros. exact (proj1 (proj2 (Private_scope_ext Γ)) e H). Qed.

Corollary Private_scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, EXP Γ ⊢ e  -> EXP  Γ' ⊢ e) /\
  (forall e, NVAL Γ ⊢ e -> NVAL Γ' ⊢ e) /\
  (forall v, VAL Γ ⊢ v  -> VAL  Γ' ⊢ v).
Proof.
  intros. induction H.
  - intuition.
  - repeat split; intros; eapply Private_scope_ext; eapply IHle; auto.
Qed.

Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof. intros. eapply Private_scope_ext_app; eauto. Qed.

Corollary scope_ext_app_val : forall Γ' Γ, Γ <= Γ' ->
  forall v, VAL Γ ⊢ v -> VAL Γ' ⊢ v.
Proof. intros. eapply Private_scope_ext_app; eauto. Qed.

Corollary scope_ext_app_nonval : forall Γ' Γ, Γ <= Γ' ->
  forall e, NVAL Γ ⊢ e -> NVAL Γ' ⊢ e.
Proof. intros. eapply Private_scope_ext_app; eauto. Qed.

(** * Well-formed runtime environments and frame stacks *)

(** A runtime environment [Γ] is well-formed when every stored value is
    closed (no dangling variable references). *)
(* Definition ENVCLOSED (Γ : Env) : Prop := Forall (fun v => VALCLOSED v) Γ. *)
Definition env_scope (Γ : Env) (n' : nat) : Prop :=
  Forall (fun v => VAL n' ⊢ v) Γ.

Notation "'ENVSCOPE' n' ⊢ Γ" := (env_scope Γ n') (at level 30).

(** * Frame scoping

    A frame is "closed" when:
    - its saved environment [Γ_saved] is well-formed, and
    - all expressions it stores are scoped with respect to the environment
      that will be active when those expressions are eventually evaluated.

    The environment sizes used below follow the semantics rules:
    - [FLet e2 Γ_saved]: [e2] is evaluated in [val :: Γ_saved], so it needs
      scope [S (length Γ_saved)].
    - [FCase p e2 e3 Γ_saved]: [e2] is evaluated in [l ++ Γ_saved] where
      [length l = pat_vars p], so scope [pat_vars p + length Γ_saved];
      [e3] is evaluated in [Γ_saved] itself, so scope [length Γ_saved].
    - All other frames evaluate their stored expressions in [Γ_saved]
      directly, so scope [length Γ_saved].
*)

Inductive FCLOSED : Frame -> Prop :=
| fclosed_app1 args Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FApp1 args Γ_saved)

| fclosed_app2 v vl args Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  VALCLOSED v ->
  Forall (fun w => VALCLOSED w) vl ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FApp2 v vl args Γ_saved)

| fclosed_let e2 Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  EXP (S (length Γ_saved)) ⊢ e2 ->
  FCLOSED (FLet e2 Γ_saved)

| fclosed_case p e2 e3 Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  EXP (pat_vars p + length Γ_saved) ⊢ e2 ->
  EXP (length Γ_saved) ⊢ e3 ->
  FCLOSED (FCase p e2 e3 Γ_saved)

| fclosed_cons1 e1 Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  EXP (length Γ_saved) ⊢ e1 ->
  FCLOSED (FCons1 e1 Γ_saved)

| fclosed_cons2 v2 Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved -> (* REDUNDANT? *)
  VALCLOSED v2 ->
  FCLOSED (FCons2 v2 Γ_saved)

| fclosed_bif1 args Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FBIF1 args Γ_saved)

| fclosed_bif2 v vl args Γ_saved :
  ENVSCOPE 0 ⊢ Γ_saved ->
  VALCLOSED v ->
  Forall (fun w => VALCLOSED w) vl ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FBIF2 v vl args Γ_saved).

Definition FSCLOSED (fs : FrameStack) : Prop := Forall (fun f => FCLOSED f) fs.

(** * Pattern matching preserves scoping *)

(**
  When [v] is scoped in [Γ] and [match_pattern p v = Some l], every value in
  [l] is also scoped in [Γ].  Proof by induction on [p]; the [PCons] case
  uses [inversion] on [scoped_cons_v] plus the two induction hypotheses.
*)
Theorem match_pattern_scoped : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Some l ->
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

(** * Well-formed environment utilities *)

Lemma ENVCLOSED_nil : ENVSCOPE 0 ⊢ [].
Proof. by constructor. Qed.

Lemma ENVCLOSED_cons : forall v Γ n, VAL n ⊢ v ->
  ENVSCOPE n ⊢ Γ -> ENVSCOPE n ⊢ (v :: Γ).
Proof. intros. apply Forall_cons; auto. Qed.

Lemma ENVCLOSED_app : forall l1 l2, ENVSCOPE 0 ⊢ l1 -> ENVSCOPE 0 ⊢ l2 -> ENVSCOPE 0 ⊢ (l1 ++ l2).
Proof. intros. apply Forall_app; auto. Qed.

Lemma ENVCLOSED_nth : forall Γ i,
  ENVSCOPE 0 ⊢ Γ -> i < length Γ -> VALCLOSED (nth i Γ (VLit 0%Z)).
Proof.
  intros Γ i Hwf. revert i.
  induction Hwf as [|v Γ' Hv Hwf' IH]; intros i Hi.
  - inversion Hi.
  - destruct i as [|i']; simpl.
    + exact Hv.
    + apply IH. simpl in Hi. lia.
Qed.

Lemma ENVCLOSED_lookup : forall Γ n v,
  ENVSCOPE 0 ⊢ Γ -> Γ !! n = Some v -> VALCLOSED v.
Proof.
  intros Γ n v Hwf. revert n v.
  induction Hwf as [|w Γ' Hw Hwf' IH]; intros n v Hlookup.
  - inversion Hlookup.
  - destruct n as [|n']; simpl in Hlookup.
    + inversion Hlookup; subst. exact Hw.
    + exact (IH n' v Hlookup).
Qed.

(**
  Equivalence between [ENVCLOSED] and the [nth]-based formulation used in
  [scoped_clos].  The (←) direction allows us to extract [ENVCLOSED Γ_env]
  from the premise of [scoped_clos] when proving [beta_reduce_scoped].
*)
Lemma ENVCLOSED_iff_nth : forall Γ,
  ENVSCOPE 0 ⊢ Γ <-> forall i, i < length Γ -> VALCLOSED (nth i Γ (VLit 0%Z)).
Proof.
  intro Γ. split.
  - intros Hwf i Hi. eapply ENVCLOSED_nth; eauto.
  - intro H.
    induction Γ as [|v Γ' IH].
    + constructor.
    + constructor.
      * exact (H 0 (Nat.lt_0_succ _)).
      * apply IH. intros i Hi. specialize (H (S i)); simpl in H; apply H; lia.
Qed.

(** * Frame stack utilities *)

Lemma FSCLOSED_nil : FSCLOSED [].
Proof. constructor. Qed.

Lemma FSCLOSED_cons : forall f fs, FCLOSED f -> FSCLOSED fs -> FSCLOSED (f :: fs).
Proof. intros. apply Forall_cons; auto. Qed.

Lemma FSCLOSED_head : forall f fs, FSCLOSED (f :: fs) -> FCLOSED f.
Proof. intros. apply Forall_inv in H. exact H. Qed.

Lemma FSCLOSED_tail : forall f fs, FSCLOSED (f :: fs) -> FSCLOSED fs.
Proof. intros. apply Forall_inv_tail in H. exact H. Qed.

(** * Scoping of closures and lookups *)

(**
  [red_fun] scoping: if the current environment is well-formed and the
  function non-value is closed, the resulting closure is closed.

  Proof: the body of [EFun vl e] is scoped in [S vl + 0 = S vl]; by
  [scope_ext_app] it is also scoped in [S vl + length Γ] as required by
  [scoped_clos].  The environment entries are closed by [ENVCLOSED_nth].
*)
Lemma red_fun_scoped : forall Γ vl e,
  ENVSCOPE 0 ⊢ Γ -> NVALCLOSED (EFun vl e) -> VALCLOSED (VClos Γ vl e).
Proof.
  intros Γ vl e Hwf Hnv.
  inversion Hnv; subst.
  apply scoped_clos.
  - intros i Hi. exact (ENVCLOSED_nth _ _ Hwf Hi).
  - eapply scope_ext_app with (Γ := S vl + 0). lia. simpl. eassumption.
Qed.

(**
  [red_var] scoping: looking up a variable in a well-formed environment
  yields a closed value.
*)
Lemma red_var_scoped : forall Γ n v,
  ENVSCOPE 0 ⊢ Γ -> Γ !! n = Some v -> VALCLOSED v.
Proof.
  intros. eapply ENVCLOSED_lookup; eauto.
Qed.

(** * Scoping of beta reduction *)

(**
  If [f] is a closed closure and [params] are a list of closed values with
  the right arity, then [beta_reduce f params = Some (Γ', e)] produces a
  well-formed environment [Γ'] and an expression [e] scoped in [length Γ'].

  Concretely, [Γ' = f :: params ++ Γ_env] and [e = body]:
  - [length Γ' = 1 + arity + length Γ_env = S arity + length Γ_env], which
    is exactly the scope index stored in [scoped_clos].
  - [ENVCLOSED Γ'] holds because [f] is closed, [params] are closed, and
    [Γ_env] is closed (extracted via [ENVCLOSED_iff_nth] from [scoped_clos]).
*)
Lemma beta_reduce_scoped : forall f params Γ' e,
  VALCLOSED f -> ENVSCOPE 0 ⊢ params ->
  beta_reduce f params = Some (Γ', e) ->
  ENVSCOPE 0 ⊢ Γ' /\ EXP (length Γ') ⊢ e.
Proof.
  intros f params Γ' e Hf Hparams Hbeta.
  destruct f as [| | | | Γ_env n_arity body];
    try (unfold beta_reduce in Hbeta; congruence).
  unfold beta_reduce in Hbeta.
  destruct (Nat.eqb (length params) n_arity) eqn:Heq; [|congruence].
  inversion Hbeta; subst. clear Hbeta.
  apply Nat.eqb_eq in Heq as Hlen.
  assert (Henv_sc : forall i, i < length Γ_env ->
      VALCLOSED (nth i Γ_env (VLit 0%Z)))
    by (inversion Hf; assumption).
  assert (Hbody_sc : EXP (S n_arity + length Γ_env) ⊢ e)
    by (inversion Hf; assumption).
  split.
  - apply ENVCLOSED_cons. exact Hf.
    apply ENVCLOSED_app. exact Hparams.
    apply ENVCLOSED_iff_nth. exact Henv_sc.
  - simpl. rewrite length_app.
    rewrite <- Hlen in Hbody_sc. exact Hbody_sc.
Qed.

Lemma eval_scope v vs res :
  eval v vs = Some res -> EXPCLOSED res.
Proof.
  intros. unfold eval in H; repeat case_match; try congruence.
  subst. inv H. do 2 constructor.
Qed.

Definition frame_scope (f : Frame) : nat :=
match f with
 | FApp1 l Γ => length Γ
 | FBIF1 l Γ => length Γ
 | FLet e2 Γ => length Γ
 | FCase p e2 e3 Γ => length Γ
 | FCons1 e1 Γ => length Γ
 | FCons2 v2 Γ => length Γ
 | FApp2 v l el Γ => length Γ
 | FBIF2 v l el Γ => length Γ
end.


Definition conf_scope (n : nat) (fs : FrameStack) (e : Exp) :=
  EXP n ⊢ e /\ Forall (fun f => frame_scope f <= n) fs.

Notation "'CONFSCOPE' n ⊢ ⟨ fs , e ⟩" := (conf_scope n fs e) (at level 5).

Lemma scope_preservation Γ fs e Γ' fs' e' :
  ⟨Γ, fs, e⟩ --> ⟨Γ', fs', e'⟩ ->
  EXP length Γ ⊢ e -> FSCLOSED fs -> ENVSCOPE 0 ⊢ Γ ->
  (forall v, e = VVal v -> VALCLOSED v) ->
  EXP length Γ' ⊢ e' /\ FSCLOSED fs' /\ ENVSCOPE 0 ⊢ Γ'.
Proof.
  intros D He Hfs HΓ Hval. inv D.
  * inv Hfs. inv H2. apply eval_scope in H.
    repeat split; try assumption.
    eapply scope_ext_app. 2: eassumption. lia.
  * inv Hfs. inv H1. inv H4.
    repeat split; try assumption.
    constructor; auto.
    constructor; auto.
  * inv Hfs. inv H1. inv H8.
    repeat split; try assumption.
    constructor; auto.
    constructor; auto.
    apply Forall_app. split; auto.
  * inv Hfs. inv H2. apply eval_scope in H.
    repeat split; try assumption.
    eapply scope_ext_app. 2: eassumption. lia.
  * inv Hfs. inv H2. apply beta_reduce_scoped in H as [].
    repeat split; try assumption.
    by apply Hval.
    apply ENVCLOSED_nil.
  * inv Hfs. inv H1. inv H4.
    repeat split; try assumption.
    constructor; auto.
    constructor; auto.
  * inv Hfs. inv H1. inv H8.
    repeat split; try assumption.
    constructor; auto.
    constructor; auto.
    apply Forall_app; split; auto.
  * inv Hfs. inv H2. apply beta_reduce_scoped in H as [].
    repeat split; try assumption.
    assumption.
    apply ENVCLOSED_app; try assumption.
    constructor; auto.
  * inv Hfs. inv H1.
    repeat split; try assumption.
    constructor; auto.
  * inv Hfs. inv H2.
    repeat split; try assumption.
    apply match_pattern_length in H.
    rewrite length_app, <- H. assumption.
    apply ENVCLOSED_app; try assumption.
    eapply match_pattern_scoped in H. exact H.
    by apply Hval.
  * inv Hfs. inv H2.
    repeat split; try assumption.
  * inv Hfs. inv H1.
    repeat split; try assumption.
    constructor; auto.
    constructor; auto.
  * inv Hfs. inv H1.
    repeat split; try assumption.
    constructor; auto. constructor; auto.
    all: eapply scope_ext_app_val with (Γ := 0); try lia.
    by apply Hval.
    assumption.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
    by eapply Forall_nth.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
    by eapply Forall_nth.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
  * inv He. inv H0.
    repeat split; try assumption.
    constructor. constructor. all: auto.
    intros.
    apply scope_ext_app_val with (Γ := 0); try lia.
    by apply ENVCLOSED_nth.
  * repeat split; try assumption.
    inv He. inv H1.
    constructor.
    apply scope_ext_app_val with (Γ := 0); try lia.
    by eapply ENVCLOSED_lookup.
Qed.

Corollary scope_preservation_any k Γ fs e Γ' fs' e' :
  ⟨Γ, fs, e⟩ -[k]-> ⟨Γ', fs', e'⟩ ->
  EXP length Γ ⊢ e -> FSCLOSED fs -> ENVSCOPE 0 ⊢ Γ ->
  (forall v, e = VVal v -> VALCLOSED v) ->
  EXP length Γ' ⊢ e' /\ FSCLOSED fs' /\ ENVSCOPE 0 ⊢ Γ'.
Admitted.
