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

Inductive ScopeSig :=
| sig_exp (n : nat) (e : Exp)
| sig_nonval (n : nat) (n : NonVal)
| sig_val (v : Val).

Inductive Scoped : ScopeSig -> Prop :=
| scoped_val v Γ :
  Scoped (sig_val v) ->
  Scoped (sig_exp Γ (VVal v))
| scoped_nonval Γ nv :
  Scoped (sig_nonval Γ nv) ->
  Scoped (sig_exp Γ (EExp nv))

(** nonvalue scoping *)
| scoped_fun Γ vl e :
  (** Before capture: body sees self + params on top of the outer env. *)
  Scoped (sig_exp (S vl + Γ) e) ->
  Scoped (sig_nonval Γ (EFun vl e))
| scoped_app Γ exp exps :
  Scoped (sig_exp Γ exp) ->
  (forall i, i < length exps -> Scoped (sig_exp Γ (nth i exps (˝VLit 0%Z)))) ->
  Scoped (sig_nonval Γ (EApp exp exps))
| scoped_let Γ e1 e2 :
  Scoped (sig_exp Γ e1) ->
  Scoped (sig_exp (S Γ) e2) ->
  Scoped (sig_nonval Γ (ELet e1 e2))
| scoped_case Γ e p e1 e2 :
  Scoped (sig_exp Γ e) ->
  Scoped (sig_exp (pat_vars p + Γ) e1) ->
  Scoped (sig_exp Γ e2) ->
  Scoped (sig_nonval Γ (ECase e p e1 e2))
| scoped_cons Γ e1 e2 :
  Scoped (sig_exp Γ e1) ->
  Scoped (sig_exp Γ e2) ->
  Scoped (sig_nonval Γ (ECons e1 e2))
| scoped_bif Γ exp exps :
  Scoped (sig_exp Γ exp) ->
  (forall i, i < length exps -> Scoped (sig_exp Γ (nth i exps (˝VLit 0%Z)))) ->
  Scoped (sig_nonval Γ (EBIF exp exps))
| scoped_var Γ n :
  n < Γ -> Scoped (sig_nonval Γ (EVar n))

(** value closedness *)

| scoped_lit l   : Scoped (sig_val (VLit l))
| scoped_pid p   : Scoped (sig_val (VPid p))
| scoped_nil     : Scoped (sig_val VNil)
| scoped_cons_v v1 v2 :
  Scoped (sig_val v1) ->
  Scoped (sig_val v2) ->
  Scoped (sig_val (VCons v1 v2))
| scoped_clos Γ_env vl e :
  (** Captured-environment values are scoped in the outer context [Γ]. *)
  (forall i, i < length Γ_env -> Scoped (sig_val (nth i Γ_env (VLit 0%Z)))) ->
  (** Body is scoped in self + params + captured-env. *)
  Scoped (sig_exp (S vl + length Γ_env) e) ->
  Scoped (sig_val (VClos Γ_env vl e)).

Notation "'EXP' Γ ⊢ e" := (Scoped (sig_exp Γ e)) (at level 69, no associativity).
Notation "'NVAL' Γ ⊢ e" := (Scoped (sig_nonval Γ e)) (at level 69, no associativity).
Notation "'VALCLOSED' v" := (Scoped (sig_val v)) (at level 69, no associativity).

Definition AnyExpScoped (Γ : nat) (e : Exp) : Prop :=
  match e with
  | VVal v => VALCLOSED v
  | EExp nv => NVAL Γ ⊢ nv
  end.

Notation "'AEXP' Γ ⊢ e" := (AnyExpScoped Γ e) (at level 69, no associativity).

Notation "'EXPCLOSED' e"  := (EXP 0 ⊢ e)  (at level 5) : env_scope.
Notation "'NVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5) : env_scope.

Global Hint Constructors Scoped  : core.
Global Hint Constructors ScopeSig  : core.


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
Lemma scope_ext_open_sig : forall s,
  Scoped s ->
  match s with
  | sig_exp Γ e => EXP (S Γ) ⊢ e
  | sig_nonval Γ nv => NVAL (S Γ) ⊢ nv
  | sig_val v => VALCLOSED v
  end.
Proof.
  intros s Hsc. induction Hsc; simpl.
  - by constructor.
  - constructor. eauto.
  - constructor.
    replace (S (S vl + Γ)) with (S vl + S Γ) in IHHsc by lia.
    exact IHHsc.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
    + exact IHHsc1.
    + replace (S (pat_vars p + Γ)) with (pat_vars p + S Γ) in IHHsc2 by lia.
      exact IHHsc2.
    + exact IHHsc3.
  - constructor; eauto.
  - constructor; eauto.
  - constructor. lia.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Corollary scope_ext : forall {e Γ},
  EXP Γ ⊢ e -> EXP (S Γ) ⊢ e.
Proof. intros. exact (scope_ext_open_sig _ H). Qed.

Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof.
  intros Γ' Γ Hle e Hsc. induction Hle.
  - exact Hsc.
  - apply scope_ext. exact IHHle.
Qed.

Lemma exp_to_any : forall Γ e,
  EXP Γ ⊢ e -> AEXP Γ ⊢ e.
Proof.
  intros Γ e Hsc. inversion Hsc; subst; simpl; assumption.
Qed.

(** * Well-formed runtime environments and frame stacks *)

(** A runtime environment [Γ] is well-formed when every stored value is
    closed (no dangling variable references). *)
Definition ENVCLOSED (Γ : Env) : Prop := Forall (fun v => VALCLOSED v) Γ.

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
  ENVCLOSED Γ_saved ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FApp1 args Γ_saved)

| fclosed_app2 v vl args Γ_saved :
  ENVCLOSED Γ_saved ->
  VALCLOSED v ->
  Forall (fun w => VALCLOSED w) vl ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FApp2 v vl args Γ_saved)

| fclosed_let e2 Γ_saved :
  ENVCLOSED Γ_saved ->
  EXP (S (length Γ_saved)) ⊢ e2 ->
  FCLOSED (FLet e2 Γ_saved)

| fclosed_case p e2 e3 Γ_saved :
  ENVCLOSED Γ_saved ->
  EXP (pat_vars p + length Γ_saved) ⊢ e2 ->
  EXP (length Γ_saved) ⊢ e3 ->
  FCLOSED (FCase p e2 e3 Γ_saved)

| fclosed_cons1 e1 Γ_saved :
  ENVCLOSED Γ_saved ->
  EXP (length Γ_saved) ⊢ e1 ->
  FCLOSED (FCons1 e1 Γ_saved)

| fclosed_cons2 v2 Γ_saved :
  ENVCLOSED Γ_saved -> (* REDUNDANT? *)
  VALCLOSED v2 ->
  FCLOSED (FCons2 v2 Γ_saved)

| fclosed_bif1 args Γ_saved :
  ENVCLOSED Γ_saved ->
  Forall (fun e => EXP (length Γ_saved) ⊢ e) args ->
  FCLOSED (FBIF1 args Γ_saved)

| fclosed_bif2 v vl args Γ_saved :
  ENVCLOSED Γ_saved ->
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
Theorem match_pattern_scoped : forall p v l,
  VALCLOSED v -> match_pattern p v = Some l ->
  Forall (fun v => VALCLOSED v) l.
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

Lemma ENVCLOSED_nil : ENVCLOSED [].
Proof. by constructor. Qed.

Lemma ENVCLOSED_cons : forall v Γ, VALCLOSED v ->
  ENVCLOSED Γ -> ENVCLOSED (v :: Γ).
Proof. intros. apply Forall_cons; auto. Qed.

Lemma ENVCLOSED_app : forall l1 l2, ENVCLOSED l1 -> ENVCLOSED l2 -> ENVCLOSED (l1 ++ l2).
Proof. intros. apply Forall_app; auto. Qed.

Lemma ENVCLOSED_nth : forall Γ i,
  ENVCLOSED Γ -> i < length Γ -> VALCLOSED (nth i Γ (VLit 0%Z)).
Proof.
  intros Γ i Hwf. revert i.
  induction Hwf as [|v Γ' Hv Hwf' IH]; intros i Hi.
  - inversion Hi.
  - destruct i as [|i']; simpl.
    + exact Hv.
    + apply IH. simpl in Hi. lia.
Qed.

Lemma ENVCLOSED_lookup : forall Γ n v,
  ENVCLOSED Γ -> Γ !! n = Some v -> VALCLOSED v.
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
  ENVCLOSED Γ <-> forall i, i < length Γ -> VALCLOSED (nth i Γ (VLit 0%Z)).
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
  ENVCLOSED Γ -> NVALCLOSED (EFun vl e) -> VALCLOSED (VClos Γ vl e).
Proof.
  intros Γ vl e Hwf Hnv.
  inversion Hnv; subst.
  apply scoped_clos.
  - intros i Hi. exact (ENVCLOSED_nth _ _ Hwf Hi).
  - eapply scope_ext_app with (Γ := S vl + 0); try lia.
    simpl. eassumption.
Qed.

(**
  [red_var] scoping: looking up a variable in a well-formed environment
  yields a closed value.
*)
Lemma red_var_scoped : forall Γ n v,
  ENVCLOSED Γ -> Γ !! n = Some v -> VALCLOSED v.
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
  VALCLOSED f -> ENVCLOSED params ->
  beta_reduce f params = Some (Γ', e) ->
  ENVCLOSED Γ' /\ EXP (length Γ') ⊢ e.
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

Lemma eval_val_scoped v vs res :
  eval v vs = Some res -> VALCLOSED res.
Proof.
  intros H. apply eval_scope in H. inversion H; assumption.
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
  AEXP n ⊢ e /\ Forall (fun f => frame_scope f <= n) fs.

Notation "'CONFSCOPE' n ⊢ ⟨ fs , e ⟩" := (conf_scope n fs e) (at level 5).

Lemma scope_preservation Γ fs e Γ' fs' e' :
  ⟨Γ, fs, e⟩ --> ⟨Γ', fs', e'⟩ ->
  AEXP length Γ ⊢ e -> FSCLOSED fs -> ENVCLOSED Γ ->
  AEXP length Γ' ⊢ e' /\ FSCLOSED fs' /\ ENVCLOSED Γ'.
Proof.
  intros D He Hfs HΓ. inv D.
  - inv Hfs. inv H2. apply eval_val_scoped in H.
    repeat split; try assumption.
  - inv Hfs. inv H1. inv H4.
    repeat split; try assumption.
    by apply exp_to_any.
    constructor.
    + econstructor; eauto.
    + assumption.
  - inv Hfs. inv H1. inv H8.
    repeat split; try assumption.
    by apply exp_to_any.
    constructor.
    + econstructor; eauto.
      apply Forall_app. split; auto.
    + assumption.
  - inv Hfs. inv H2. apply eval_val_scoped in H.
    repeat split; try assumption.
  - inv Hfs. inv H2.
    simpl in He. assert (Hv : VALCLOSED v) by exact He.
    pose proof (beta_reduce_scoped _ _ _ _ Hv ENVCLOSED_nil H) as [HΓ' Hbody].
    repeat split; try assumption.
    by apply exp_to_any.
  - inv Hfs. inv H1. inv H4.
    repeat split; try assumption.
    by apply exp_to_any.
    constructor.
    + econstructor; eauto.
    + assumption.
  - inv Hfs. inv H1. inv H8.
    repeat split; try assumption.
    by apply exp_to_any.
    constructor.
    + econstructor; eauto.
      apply Forall_app; split; auto.
    + assumption.
  - inv Hfs. inv H2.
    simpl in He. assert (Hv0 : VALCLOSED v0) by exact He.
    assert (Hparams : ENVCLOSED (vl ++ [v0])).
    { apply ENVCLOSED_app; try assumption. constructor; auto. }
    pose proof (beta_reduce_scoped _ _ _ _ H7 Hparams H) as [HΓ' Hbody].
    repeat split; try assumption.
    by apply exp_to_any.
  - inv Hfs. inv H1.
    repeat split; try assumption.
    by apply exp_to_any.
    eapply ENVCLOSED_cons; eauto.
  - inv Hfs. inv H2.
    repeat split; try assumption.
    apply match_pattern_length in H.
    rewrite length_app, <- H. by apply exp_to_any.
    apply ENVCLOSED_app; try assumption.
    eapply match_pattern_scoped in H. exact H.
    by simpl in He.
  - inv Hfs. inv H2.
    repeat split; try assumption.
    by apply exp_to_any.
  - inv Hfs. inv H1.
    repeat split; try assumption.
    by apply exp_to_any.
    eapply FSCLOSED_cons.
    + apply fclosed_cons2.
      * exact H3.
      * by simpl in He.
    + exact H2.
  - inv Hfs. inv H1.
    repeat split; try assumption.
    simpl. constructor.
    + exact He.
    + assumption.
  - simpl in He. inv He.
    split.
    + by apply exp_to_any.
    + split.
      * constructor.
        -- econstructor; eauto.
        -- assumption.
      * assumption.
  - simpl in He. inv He.
    split.
    + by apply exp_to_any.
    + split.
      * constructor.
        -- econstructor; eauto.
           by eapply Forall_nth.
        -- assumption.
      * assumption.
  - simpl in He. inv He.
    split.
    + by apply exp_to_any.
    + split.
      * constructor.
        -- econstructor; eauto.
           by eapply Forall_nth.
        -- assumption.
      * assumption.
  - simpl in He. inv He.
    split.
    + by apply exp_to_any.
    + split.
      * constructor.
        -- econstructor; eauto.
        -- assumption.
      * assumption.
  - simpl in He. inv He.
    split.
    + by apply exp_to_any.
    + split.
      * constructor.
        -- econstructor; eauto.
        -- assumption.
      * assumption.
  - simpl in He. inv He.
    repeat split; try assumption.
    simpl. econstructor.
    + intros i Hi. eapply ENVCLOSED_nth; eauto.
    + eassumption.
  - simpl in He. inv He.
    repeat split; try assumption.
    simpl. eapply ENVCLOSED_lookup; eauto.
Qed.

Corollary scope_preservation_any k Γ fs e Γ' fs' e' :
  ⟨Γ, fs, e⟩ -[k]-> ⟨Γ', fs', e'⟩ ->
  AEXP length Γ ⊢ e -> FSCLOSED fs -> ENVCLOSED Γ ->
  AEXP length Γ' ⊢ e' /\ FSCLOSED fs' /\ ENVCLOSED Γ'.
Proof.
  intro Hrt. induction Hrt; intros Hsc Hfs HΓ.
  * by repeat split.
  * apply scope_preservation in H as [Hsc' [Hfs' HΓ']]; try assumption.
    eapply IHHrt; eauto.
Qed.
