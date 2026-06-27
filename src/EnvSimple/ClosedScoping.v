(**
  Closed scoping for the wrapper-free environment semantics.
*)

From CoreErlang.EnvSimple Require Export Semantics.
Import ListNotations.
Open Scope env_simple_scope.

Inductive ExpScoped : nat -> Exp -> Prop :=
| scoped_fun Γ vl e :
    ExpScoped (S vl + Γ) e ->
    ExpScoped Γ (EFun vl e)
| scoped_app Γ exp exps :
    ExpScoped Γ exp ->
    (forall i, i < length exps ->
      ExpScoped Γ (nth i exps (ELit (Int 0%Z)))) ->
    ExpScoped Γ (EApp exp exps)
| scoped_let Γ e1 e2 :
    ExpScoped Γ e1 ->
    ExpScoped (S Γ) e2 ->
    ExpScoped Γ (ELet e1 e2)
| scoped_case Γ e p e1 e2 :
    ExpScoped Γ e ->
    ExpScoped (pat_vars p + Γ) e1 ->
    ExpScoped Γ e2 ->
    ExpScoped Γ (ECase e p e1 e2)
| scoped_cons Γ e1 e2 :
    ExpScoped Γ e1 ->
    ExpScoped Γ e2 ->
    ExpScoped Γ (ECons e1 e2)
| scoped_bif Γ exp exps :
    ExpScoped Γ exp ->
    (forall i, i < length exps ->
      ExpScoped Γ (nth i exps (ELit (Int 0%Z)))) ->
    ExpScoped Γ (EBIF exp exps)
| scoped_var Γ n :
    n < Γ ->
    ExpScoped Γ (EVar n)
| scoped_lit Γ l :
    ExpScoped Γ (ELit l)
| scoped_pid Γ p :
    ExpScoped Γ (EPid p)
| scoped_nil Γ :
    ExpScoped Γ ENil.

Inductive ValClosed : Val -> Prop :=
| scoped_vlit l :
    ValClosed (VLit l)
| scoped_vpid p :
    ValClosed (VPid p)
| scoped_vnil :
    ValClosed VNil
| scoped_vcons v1 v2 :
    ValClosed v1 ->
    ValClosed v2 ->
    ValClosed (VCons v1 v2)
| scoped_clos Γ_env vl e :
    (forall i, i < length Γ_env ->
      ValClosed (nth i Γ_env (VLit (Int 0%Z)))) ->
    ExpScoped (S vl + length Γ_env) e ->
    ValClosed (VClos Γ_env vl e).

Notation "'EXP' Γ ⊢ e" := (ExpScoped Γ e)
  (at level 69, no associativity) : env_simple_scope.
Notation "'VALCLOSED' v" := (ValClosed v)
  (at level 5, no associativity) : env_simple_scope.
Notation "'EXPCLOSED' e" := (EXP 0 ⊢ e)
  (at level 5, no associativity) : env_simple_scope.

Global Hint Constructors ExpScoped ValClosed : core.

Corollary scope_ext : forall {e Γ},
  EXP Γ ⊢ e -> EXP (S Γ) ⊢ e.
Proof.
  intros e Γ Hsc. induction Hsc.
  - constructor.
    replace (S vl + S Γ) with (S (S vl + Γ)) by lia.
    exact IHHsc.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
    replace (pat_vars p + S Γ) with (S (pat_vars p + Γ)) by lia.
    exact IHHsc2.
  - constructor; eauto.
  - constructor; eauto.
  - constructor. lia.
  - constructor.
  - constructor.
  - constructor.
Qed.

Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof.
  intros Γ' Γ Hle e Hsc. induction Hle.
  - exact Hsc.
  - apply scope_ext. exact IHHle.
Qed.

Definition ENVCLOSED (Γ : Env) : Prop :=
  Forall (fun v => VALCLOSED v) Γ.

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
    ENVCLOSED Γ_saved ->
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

Definition FSCLOSED (fs : FrameStack) : Prop := Forall FCLOSED fs.

Lemma FSCLOSED_head : forall f fs, FSCLOSED (f :: fs) -> FCLOSED f.
Proof. intros. apply Forall_inv in H. exact H. Qed.

Lemma FSCLOSED_tail : forall f fs, FSCLOSED (f :: fs) -> FSCLOSED fs.
Proof. intros. apply Forall_inv_tail in H. exact H. Qed.

Theorem match_pattern_scoped : forall p v lv,
  VALCLOSED v -> match_pattern p v = Some lv ->
  Forall (fun v => VALCLOSED v) lv.
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

Lemma ENVCLOSED_nil : ENVCLOSED [].
Proof. constructor. Qed.

Lemma ENVCLOSED_cons : forall v Γ,
  VALCLOSED v -> ENVCLOSED Γ -> ENVCLOSED (v :: Γ).
Proof. intros. constructor; auto. Qed.

Lemma ENVCLOSED_app : forall l1 l2,
  ENVCLOSED l1 -> ENVCLOSED l2 -> ENVCLOSED (l1 ++ l2).
Proof. intros. apply Forall_app; auto. Qed.

Lemma ENVCLOSED_nth : forall Γ i,
  ENVCLOSED Γ -> i < length Γ -> VALCLOSED (nth i Γ (VLit (Int 0%Z))).
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

Lemma ENVCLOSED_iff_nth : forall Γ,
  ENVCLOSED Γ <-> forall i, i < length Γ -> VALCLOSED (nth i Γ (VLit (Int 0%Z))).
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

Lemma red_fun_scoped : forall Γ vl e,
  ENVCLOSED Γ -> EXPCLOSED (EFun vl e) -> VALCLOSED (VClos Γ vl e).
Proof.
  intros Γ vl e Hwf Hfun.
  inversion Hfun; subst.
  eapply scoped_clos.
  - intros i Hi. exact (ENVCLOSED_nth _ _ Hwf Hi).
  - eapply scope_ext_app with (Γ := S vl + 0); try lia.
    simpl. assumption.
Qed.

Lemma red_var_scoped : forall Γ n v,
  ENVCLOSED Γ -> Γ !! n = Some v -> VALCLOSED v.
Proof.
  intros. eapply ENVCLOSED_lookup; eauto.
Qed.

Lemma beta_reduce_scoped : forall f params Γ' e,
  VALCLOSED f -> ENVCLOSED params ->
  beta_reduce f params = Some (Γ', e) ->
  ENVCLOSED Γ' /\ EXP (length Γ') ⊢ e.
Proof.
  intros f params Γ' e Hf Hparams Hbeta.
  destruct f as [| | | | Γ_env arity body];
    try (unfold beta_reduce in Hbeta; congruence).
  unfold beta_reduce in Hbeta.
  destruct (Nat.eqb (length params) arity) eqn:Heq; [|congruence].
  inversion Hbeta; subst. clear Hbeta.
  apply Nat.eqb_eq in Heq as Hlen.
  assert (Henv_sc : forall i, i < length Γ_env ->
    VALCLOSED (nth i Γ_env (VLit (Int 0%Z))))
    by (inversion Hf; assumption).
  assert (Hbody_sc : EXP (S arity + length Γ_env) ⊢ e)
    by (inversion Hf; assumption).
  split.
  - apply ENVCLOSED_cons. exact Hf.
    apply ENVCLOSED_app. exact Hparams.
    apply ENVCLOSED_iff_nth. exact Henv_sc.
  - simpl. rewrite length_app. rewrite <- Hlen in Hbody_sc. exact Hbody_sc.
Qed.

Lemma eval_val_scoped : forall v vs res,
  eval v vs = Some res -> VALCLOSED res.
Proof.
  intros v vs res H.
  unfold eval in H. repeat break_match_hyp; try congruence.
  inversion H; subst; constructor.
Qed.

Definition frame_scope (f : Frame) : nat :=
  match f with
  | FApp1 _ Γ => length Γ
  | FBIF1 _ Γ => length Γ
  | FLet _ Γ => length Γ
  | FCase _ _ _ Γ => length Γ
  | FCons1 _ Γ => length Γ
  | FCons2 _ Γ => length Γ
  | FApp2 _ _ _ Γ => length Γ
  | FBIF2 _ _ _ Γ => length Γ
  end.

Definition runtime_scope (n : nat) (t : Runtime) : Prop :=
  match t with
  | RExp e => EXP n ⊢ e
  | RVal v => VALCLOSED v
  end.

Definition conf_scope (n : nat) (fs : FrameStack) (t : Runtime) : Prop :=
  runtime_scope n t /\ Forall (fun f => frame_scope f <= n) fs.

Notation "'CONFSCOPE' n ⊢ ⟨ fs , t ⟩" := (conf_scope n fs t)
  (at level 5) : env_simple_scope.

Lemma scope_preservation : forall Γ fs t Γ' fs' t',
  ⟨ Γ, fs, t ⟩ --> ⟨ Γ', fs', t' ⟩ ->
  runtime_scope (length Γ) t -> FSCLOSED fs -> ENVCLOSED Γ ->
  runtime_scope (length Γ') t' /\ FSCLOSED fs' /\ ENVCLOSED Γ'.
Admitted.

Corollary scope_preservation_any : forall k Γ fs t Γ' fs' t',
  ⟨ Γ, fs, t ⟩ -[k]-> ⟨ Γ', fs', t' ⟩ ->
  runtime_scope (length Γ) t -> FSCLOSED fs -> ENVCLOSED Γ ->
  runtime_scope (length Γ') t' /\ FSCLOSED fs' /\ ENVCLOSED Γ'.
Admitted.
