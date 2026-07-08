From CoreErlang.Env Require Import ClosedScoping.
From CoreErlang.Subst Require Import Semantics.

(** Module aliases to disambiguate between environment-based and
    substitution-based syntax/semantics types. *)
Module ESyn := Env.Syntax.
Module ESem := Env.Semantics.

(**
  Conversion from environment-based values/expressions to
  substitution-based ones.

  The core insight:
  - [VClos Γ vl body] captures its environment explicitly.
    We eliminate [Γ] by substituting it into the body: variables
    [0..vl] stay bound (0 = self, 1..vl = params), and variables
    [S vl + k] are replaced by the converted value [Γ[k]].
  - [EFun vl body] (a NonVal in Env) becomes [VFun vl body] (a Val in Sub),
    since function expressions are immediately values in the Sub system.
  - [VVar n] (a variable lookup via the environment) is handled by
    [convert_env], which turns the runtime environment list into a
    substitution that is applied to the converted expression.
*)
Fixpoint convert_val (v : ESyn.Val) : Val :=
  match v with
  | ESyn.VLit l      => VLit l
  | ESyn.VPid p      => VPid p
  | ESyn.VNil        => VNil
  | ESyn.VCons v1 v2 => VCons (convert_val v1) (convert_val v2)
  | ESyn.VClos Γ vl body =>
      (** Variables [S vl + k] in [body] refer to [Γ[k]]; substitute them away.
          [upn (S vl)] leaves variables [0..vl] (self + params) untouched. *)
      VFun vl ((convert_exp body).[upn (S vl) (list_subst (map convert_val Γ) idsubst)])
  end

(** Structurally convert an Env expression to a Sub expression.
    The current environment [Γ] is NOT applied here; use [convert_env]
    and apply it separately (see [convert_frame] and [env_to_sub]). *)
with convert_exp (e : ESyn.Exp) : Exp :=
  match e with
  | ESyn.VVal v  => VVal (convert_val v)
  | ESyn.EExp nv => convert_nv nv
  end

with convert_nv (nv : ESyn.NonVal) : Exp :=
  match nv with
  | ESyn.EFun vl body    => VVal (VFun vl (convert_exp body))
  | ESyn.EApp f args     => EExp (EApp (convert_exp f) (map convert_exp args))
  | ESyn.ELet e1 e2      => EExp (ELet (convert_exp e1) (convert_exp e2))
  | ESyn.ECase e p e1 e2 => EExp (ECase (convert_exp e) p (convert_exp e1) (convert_exp e2))
  | ESyn.ECons e1 e2     => EExp (ECons (convert_exp e1) (convert_exp e2))
  | ESyn.EBIF f args     => EExp (EBIF (convert_exp f) (map convert_exp args))
  | ESyn.EVar n          => VVar n
  end.

(** Turn a runtime environment (a list of Env values) into a substitution
    suitable for Sub expressions. Applying this to [convert_exp e] yields
    the Sub expression that corresponds to evaluating [e] in [Γ]. *)
Definition convert_env (Γ : ESem.Env) : Substitution :=
  list_subst (map convert_val Γ) idsubst.

(**
  Convert an environment-based frame to a substitution-based frame.

  Each Env frame stores a saved environment [Γ] that will become the
  active environment when the frame is popped. We bake [Γ] into the
  frame's subexpressions as a substitution so the Sub frame needs no
  environment:

  - For [FLet e2 Γ]: the body [e2] will be evaluated with ONE new
    binding prepended to [Γ], so we shift [Γ] by 1 with [up_subst],
    leaving variable 0 free for the incoming let-bound value.

  - For [FCase p e2 e3 Γ]: [e2] will be evaluated with [pat_vars p]
    new bindings prepended to [Γ], so we use [upn (pat_vars p)] to
    leave those pattern variables free; [e3] uses [Γ] directly.

  - For all other frames, the stored [Γ] is applied as [convert_env Γ]
    to each unevaluated subexpression.
*)
Definition convert_frame (f : ESem.Frame) : Frame :=
  match f with
  | ESem.FApp1 args Γ =>
      FApp1 (map (fun e => (convert_exp e).[convert_env Γ]) args)
  | ESem.FApp2 v vl args Γ =>
      (** Env accumulates evaluated args by prepending (newest-first), while
          Sub accumulates by appending (oldest-first).  Reversing [vl] here
          reconciles the two orders so that [app2_step] / [red_app2] work. *)
      FApp2 (convert_val v).ᵥ[convert_env Γ]
            (map (subst_val (convert_env Γ) ∘ convert_val) vl)
            (map (fun e => (convert_exp e).[convert_env Γ]) args)
  | ESem.FLet e2 Γ =>
      FLet ((convert_exp e2).[up_subst (convert_env Γ)])
  | ESem.FCase p e2 e3 Γ =>
      FCase p ((convert_exp e2).[upn (pat_vars p) (convert_env Γ)])
              ((convert_exp e3).[convert_env Γ])
  | ESem.FCons1 e1 Γ =>
      FCons1 ((convert_exp e1).[convert_env Γ])
  | ESem.FCons2 v2 Γ =>
      FCons2 (convert_val v2).ᵥ[convert_env Γ]
  | ESem.FBIF1 args Γ =>
      FBIF1 (map (fun e => (convert_exp e).[convert_env Γ]) args)
  | ESem.FBIF2 v vl args Γ =>
      FBIF2 (convert_val v).ᵥ[convert_env Γ]
            (map (subst_val (convert_env Γ) ∘ convert_val) vl)
            (map (fun e => (convert_exp e).[convert_env Γ]) args)
  end.

Definition convert_framestack (Fs : ESem.FrameStack) : FrameStack :=
  map convert_frame Fs.


(* (** Looking up variable [n] in the converted environment gives [convert_val] of
    the [n]-th environment entry. *)
Lemma convert_env_lookup_var Γ n v :
  Γ !! n = Some v →
  (VVal (VVar n)).[convert_env Γ] = VVal (convert_val v).
Proof.
  intro Hn.
  apply lookup_lt_Some in Hn as Hlt.
  cbn. unfold convert_env.
  rewrite list_subst_lt by (rewrite length_map; exact Hlt).
  f_equal.
  setoid_rewrite map_nth with (f := convert_val) (d := ESyn.VLit 0%Z).
  apply f_equal.
  by apply nth_lookup_Some.
Qed. *)

(** [list_subst] distributes over list concatenation:
    substituting a concatenated list is the same as substituting in two
    stages, one list at a time. *)
Lemma list_subst_concat (l1 l2 : list Val) (ξ : Substitution) :
  list_subst l1 (list_subst l2 ξ) = list_subst (l1 ++ l2) ξ.
Proof.
  induction l1; cbn; auto.
  extensionality n. destruct n; cbn; auto.
  exact (equal_f IHl1 n).
Qed.

(** Pattern matching commutes with [convert_val] (success case). *)
Lemma match_pattern_convert p v l :
  ESyn.match_pattern p v = Some l →
  match_pattern p (convert_val v) = Some (map convert_val l).
Proof.
  revert v l. induction p; intros; destruct v; cbn in *; try (by congruence).
  all: try by inv H.
  - (* PLit l0 *)
    case_match; inv H. reflexivity.
  - (* PPid p0 *)
    case_match; inv H.
    reflexivity.
  - (* PCons p1 p2 *)
    case_match. 2: congruence.
    case_match. 2: congruence.
    inv H.
    apply IHp1 in H0.
    apply IHp2 in H1.
    rewrite H0, H1.
    by rewrite map_app.
Qed.

(** Pattern matching commutes with [convert_val] (failure case). *)
Lemma match_pattern_convert_none p v :
  ESyn.match_pattern p v = None →
  match_pattern p (convert_val v) = None.
Proof.
  revert v. induction p; destruct v; intros; cbn in *; try by congruence.
  * case_match; by congruence.
  * case_match; by congruence.
  * repeat case_match; try congruence.
    - apply IHp2 in H1. congruence.
    - apply IHp1 in H0. congruence.
Qed.

(** The converted environment of a concatenation equals first substituting
    the converted [l] values and then the converted [Γ] values. *)
Lemma convert_env_app l Γ :
  convert_env (l ++ Γ) = list_subst (map convert_val l) (convert_env Γ).
Proof.
  unfold convert_env. rewrite map_app. apply eq_sym, list_subst_concat.
Qed.

(** Characterise the only possible result of [ESem.eval]:
    the only BIF is ["+"] applied to two integers. *)
Lemma eval_characterize v l res :
  ESem.eval v l = Some res →
  ∃ z1 z2, v = ESyn.VLit (Atom "+") ∧
           l = [ESyn.VLit (Int z1); ESyn.VLit (Int z2)] ∧
           res = ESyn.VLit (Int (z1 + z2)).
Proof.
  intros H. unfold ESem.eval in H.
  repeat case_match; try discriminate; subst.
  inv H. eauto.
Qed.

(** Conversion respects Sub scoping: Env scoping of an expression implies
    Sub scoping of its conversion. *)
Lemma convert_aexp_scoped : forall sig,
  Scoped sig ->
    match sig with
    | sig_exp Γ e => EXP Γ ⊢ convert_exp e
    | sig_nonval Γ e => EXP Γ ⊢ convert_nv e
    | sig_val e => VALCLOSED (convert_val e)
    end.
Proof.
  intros sig Hsc. induction Hsc; simpl in *.
  - constructor.
    eapply (scope_ext_app_val Γ 0); [lia | exact IHHsc].
  - exact IHHsc.
  - constructor. constructor. exact IHHsc.
  - constructor. constructor.
    + exact IHHsc.
    + intros i Hi.
      pose proof (length_map convert_exp exps) as Hlen.
      rewrite nth_indep with
        (d' := convert_exp (ESyn.VVal (ESyn.VLit (Int 0)))) by lia.
      rewrite map_nth.
      apply H0. lia.
  - constructor. constructor; auto.
  - constructor. constructor; auto.
  - constructor. constructor; auto.
  - constructor. constructor.
    + exact IHHsc.
    + intros i Hi.
      pose proof (length_map convert_exp exps) as Hlen.
      rewrite nth_indep with
        (d' := convert_exp (ESyn.VVal (ESyn.VLit (Int 0)))) by lia.
      rewrite map_nth.
      apply H0. lia.
  - constructor. constructor. exact H.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply scoped_fun.
    apply (proj1 (subst_preserves_scope_exp _ _) IHHsc).
    refine (upn_scope (S vl) (length Γ_env) 0
      (list_subst (map convert_val Γ_env) idsubst) _).
    rewrite <- length_map with (f := convert_val).
    apply scoped_list_idsubst.
    assert (
      forall l,
        (forall i, i < length l ->
          VALCLOSED (convert_val (nth i l (ESyn.VLit (Int 0))))) ->
        Forall (fun v => VALCLOSED v) (map convert_val l)
    ) as Hall.
    { intros l Hvals. induction l as [|v rest IH].
      - constructor.
      - simpl. constructor.
        + exact (Hvals 0 ltac:(simpl; lia)).
        + apply IH. intros i Hi. exact (Hvals (S i) ltac:(simpl; lia)).
    }
    exact (Hall Γ_env H0).
Qed.

Corollary convert_scoped_aexp :
  forall sig,
    Scoped sig ->
      match sig with
      | sig_exp Γ e => EXP Γ ⊢ convert_exp e
      | sig_nonval Γ e => EXP Γ ⊢ convert_nv e
      | sig_val e => VALCLOSED (convert_val e)
      end.
Proof.
  exact convert_aexp_scoped.
Qed.

Corollary convert_scoped_exp :
  forall Γ,
  (forall e,  (EXP Γ ⊢ e)%env  → EXP Γ ⊢ convert_exp e).
Proof.
  intros Γ e Hsc. exact (convert_aexp_scoped _ Hsc).
Qed.

Corollary convert_scoped_nval :
  forall Γ,
  (forall e,  (NVAL Γ ⊢ e)%env  → EXP Γ ⊢ convert_nv e).
Proof.
  intros Γ e Hsc. exact (convert_aexp_scoped _ Hsc).
Qed.

Corollary convert_scoped_val :
  forall e, (VALCLOSED e)%env → VALCLOSED (convert_val e).
Proof.
  intros e Hsc. exact (convert_aexp_scoped _ Hsc).
Qed.

Corollary convert_scoped :
  forall e, (VALCLOSED e)%env → VALCLOSED (convert_val e).
Proof.
  exact convert_scoped_val.
Qed.

(** Applying a substitution to each [convert_val] in a list is a no-op
    when all elements are well-formed (closed). *)
Lemma map_wf_val_subst_id (l : list ESyn.Val) σ :
  Forall (fun v => VALCLOSED v)%env l →
  map (subst_val σ ∘ convert_val) l = map convert_val l.
Proof.
  induction l; intro H; [reflexivity|].
  inv H. cbn. f_equal.
  - rewrite closed_ignores_sub_val. reflexivity.
    by apply convert_scoped.
  - exact (IHl H3).
Qed.


(** The convert_env of a well-formed environment is a well-scoped substitution.
    Proved here as a standalone lemma to avoid evar-unification issues inside
    the main [env_to_sub] proof. *)
Lemma ENVCLOSED_scoped_list : forall Γ,
  ENVCLOSED Γ →
  SUBSCOPE (length Γ) ⊢ convert_env Γ ∷ 0.
Proof.
  intros Γ HwfΓ. unfold convert_env, ENVCLOSED in *.
  rewrite <- length_map with (f := convert_val).
  apply scoped_list_idsubst.
  induction HwfΓ; constructor; auto.
  by apply convert_scoped.
Qed.

(* ------------------------------------------------------------------ *)
(*  Main theorem                                                       *)
(* ------------------------------------------------------------------ *)

(**
  Every step in the environment-based semantics corresponds to zero or
  more steps in the substitution-based semantics after applying the
  conversion functions.

  Two Env rules produce zero Sub steps ([k = 0]):
  - [red_fun]:  [EFun vl e] already converts to the closed value
    [VFun vl body'] — no Sub step is needed.
  - [red_var]:  [VVar n] is already substituted to [convert_val (Γ !! n)]
    by [convert_env] — no Sub step is needed.
  All other rules that are proved correspond to exactly one Sub step
  ([k = 1]).

  Three cases are currently [Admitted] because they require additional
  infrastructure not yet developed:
  - [red_app_params]: for arity ≥ 3, the body's variable indexing in the
    Env semantics is the reverse of the Sub semantics; requires a deeper
    analysis of [beta_reduce] and its interaction with substitution.
  - [red_bif_params]:  complex string-level case-analysis on the built-in
    function name is deferred.
  - [red_fun]: requires an env-scoping result
    ([EXP (S vl + |Γ|) ⊢ convert_exp body]) not yet proved.
*)

Definition sub_frame (σ : Substitution) (f : Frame) : Frame :=
match f with
 | FApp1 l => FApp1 (map (subst σ) l)
 | FApp2 v l1 l2 => FApp2 (subst_val σ v) (map (subst_val σ) l1) (map (subst σ) l2)
 | FLet e2 => FLet (subst (up_subst σ) e2)
 | FCase p e2 e3 => FCase p (subst (upn (pat_vars p) σ) e2) (subst σ e3)
 | FCons1 e1 => FCons1 (subst σ e1)
 | FCons2 v2 => FCons2 (subst_val σ v2)
 | FBIF1 l => FBIF1 (map (subst σ) l)
 | FBIF2 v l1 l2 =>  FBIF2 (subst_val σ v) (map (subst_val σ) l1) (map (subst σ) l2)
end.


Definition sub_stack (σ : Substitution) (fs : FrameStack) :=
map (sub_frame σ) fs.

Lemma env_to_sub :
  forall Γ (Fs : ESem.FrameStack) e Γ' Fs' e',
  ENVCLOSED Γ →
  ClosedScoping.FSCLOSED Fs ->
  (EXP length Γ ⊢ e)%env →
  ⟨Γ, Fs, e⟩ --> ⟨Γ', Fs', e'⟩ ->
  exists k,
  ⟨convert_framestack Fs, (convert_exp e).[convert_env Γ]⟩
    -[k]->
  ⟨convert_framestack Fs', (convert_exp e').[convert_env Γ']⟩ /\ k <= 1.
Proof.
  intros * HwfΓ HwfFs Hscoped D. inv D; cbn.
  * destruct v; simpl in *; try congruence.
    destruct l. 2: congruence.
    case_match. congruence.
    repeat case_match; congruence.
  * exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite 2! (closed_ignores_sub_val (convert_val v)).
    2-3: by apply convert_scoped; inv Hscoped.
    constructor.
  * exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_app. simpl.
    rewrite 2! (closed_ignores_sub_val (convert_val v0)).
    2-3: by apply convert_scoped; inv Hscoped.
    constructor.
  * (* red_bif_params: eval v (vl ++ [v0]) = Some res *)
    inv HwfFs.
    apply eval_characterize in H as (z1 & z2 & -> & Hvleq & ->).
    destruct vl as [|w [|? ?]]; try discriminate.
    2: { inv Hvleq. apply f_equal with (f := length) in H4.
         rewrite length_app in H4. simpl in H4. lia.
       }
    simpl in Hvleq. inv Hvleq. simpl.
    exists 1. split. 2: lia.
    econstructor. constructor. constructor.
  * (* red_app0: beta_reduce v [] = Some (Γ', res) *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val _ _). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    destruct v; cbn in H; try discriminate.
    destruct vl; try congruence.
    inv H.
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite subst_comp, subst_extend, substcomp_id_r.
    constructor.
  * (* red_app: start evaluating first argument *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    constructor.
  * (* step_app_params: accumulate evaluated argument *)
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_app. simpl.
    rewrite 2! (closed_ignores_sub_val (convert_val v0)).
    2-3: by apply convert_scoped; inv Hscoped.
    constructor.
  * (* red_app_params: beta_reduce v (vl ++ [v0]) = Some (Γ', res) *)
    inv HwfFs.
    destruct v; cbn in H; try discriminate.
    destruct (Nat.eqb_spec (length (vl ++ [v0])) vl0) as [Hn|]; [|discriminate].
    inv H.
    rewrite (closed_ignores_sub_val). 2: {
      apply convert_scoped. by inv H2.
    }
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    rewrite (map_wf_val_subst_id).
    2: { by inv H2. }
    cbn [convert_val].
    exists 1. split. 2: lia.
    econstructor.
    - apply red_app2.
      rewrite length_map.
      rewrite length_app. simpl. lia.
    - rewrite subst_comp.
      simpl.
      rewrite substcomp_scons.
      rewrite subst_list_extend. 2: { rewrite 2! length_app, length_map. simpl. lia. }
      rewrite list_subst_concat.
      cbn.
      rewrite 2!map_app. constructor.
  * (* red_let: pop let frame and extend environment *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite subst_comp, subst_extend, substcomp_id_r.
    constructor.
  * (* red_case_true: pattern matches, extend env with bindings *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    pose proof (ESyn.match_pattern_length _ _ _ H) as Hlen.
    apply match_pattern_convert in H.
    cbn.
    exists 1. split. 2: lia.
    econstructor.
    - apply red_case_true. exact H.
    - rewrite subst_comp.
      enough (upn (pat_vars p) (convert_env Γ1) >>
              list_subst (map convert_val l) idsubst
              = convert_env (l ++ Γ1)) as HE.
      { rewrite HE. constructor. }
      rewrite convert_env_app.
      rewrite subst_list_extend. reflexivity.
      by rewrite length_map.
  * (* red_case_false: pattern fails, fall through *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    apply match_pattern_convert_none in H.
    cbn.
    exists 1. split. 2: lia.
    econstructor. apply red_case_false. exact H.
    constructor.
  * (* red_cons1: push second element frame *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    constructor.
  * (* red_cons2: build the cons cell *)
    inv HwfFs. inv H1.
    rewrite (closed_ignores_sub_val). 2: by apply convert_scoped.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val). 2: {
      by apply convert_scoped; inv Hscoped.
    }
    constructor.
  * (* step_let: push let frame *)
    exists 1. split. 2: lia.
    econstructor. constructor. constructor.
  * (* step_app: push app frame *)
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_map.
    constructor.
  * (* step_bif: push bif frame *)
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_map.
    constructor.
  * (* step_case: push case frame *)
    exists 1. split. 2: lia.
    econstructor. constructor. constructor.
  * (* step_cons: push cons frame *)
    exists 1. split. 2: lia.
    econstructor. constructor. constructor.
  * simpl.
    replace (VFun _ _.[_].[_]) with
      ((VFun vl (convert_exp e0)).ᵥ[convert_env Γ'].ᵥ[convert_env Γ']) by reflexivity.
    rewrite (closed_ignores_sub_val ((VFun vl (convert_exp e0)).ᵥ[convert_env Γ'])).
    - exists 0. split. constructor. lia.
    - apply -> subst_preserves_scope_val.
      + constructor. inv Hscoped. inv H0.
        apply convert_scoped_exp. eassumption.
      + apply ENVCLOSED_scoped_list. assumption.
  * (* red_var: look up variable in environment *)
    apply lookup_lt_Some in H as Hlt.
    exists 0. split. 2: lia.
    unfold convert_env.
    rewrite list_subst_lt by (rewrite length_map; exact Hlt).
    rewrite map_nth with (d := ESyn.VLit (Int 0)).
    erewrite (nth_lookup_Some). 2: eassumption.
    rewrite closed_ignores_sub_val. constructor.
    apply convert_scoped.
    eapply Forall_lookup_1 in H. 2: exact HwfΓ.
    assumption.
Qed.


(**
  Inverse conversion: from substitution-based syntax back to
  environment-based syntax.

  These functions return [option] so that partial/undefined cases are
  handled cleanly instead of returning dummy values.  The callers may
  assume that the Sub term is *closed* (no free [VVar] occurrences),
  which is guaranteed for any term that lies in the image of
  [convert_val] / [convert_exp].

  Partial cases that yield [None]:
  - [VVar n]    — not in the image of [convert_val]; free variable.
  - [EReceive]  — has no counterpart in the Env syntax.

  [VFun vl e] recovers [VClos [] vl body] with an empty environment,
  since the original environment was baked into the body by substitution
  and cannot be recovered.
*)


Fixpoint inv_convert_val (v : Val) : option ESyn.Val :=
  match v with
  | VLit l      => Some (ESyn.VLit l)
  | VPid p      => Some (ESyn.VPid p)
  | VNil        => Some ESyn.VNil
  | VCons v1 v2 =>
      match inv_convert_val v1, inv_convert_val v2 with
      | Some v1', Some v2' => Some (ESyn.VCons v1' v2')
      | _,        _        => None
      end
  | VVar _      => None   (* free variable; not in image of convert_val *)
  | VFun vl e   =>
      match inv_convert_exp e with
      | Some e' => Some (ESyn.VClos [] vl e')
      | None    => None
      end
  end
with inv_convert_exp (e : Exp) : option ESyn.Exp :=
  match e with
  | VVal v => ESyn.VVal <$> inv_convert_val v
  | EExp nv => ESyn.EExp <$> inv_convert_nv nv
  end
with inv_convert_nv (nv : NonVal) : option ESyn.NonVal :=
  match nv with
  | EApp f args =>
      match inv_convert_exp f, mapM inv_convert_exp args with
      | Some f', Some args' => Some (ESyn.EApp f' args')
      | _,       _          => None
      end
  | ELet e1 e2 =>
      match inv_convert_exp e1, inv_convert_exp e2 with
      | Some e1', Some e2' => Some (ESyn.ELet e1' e2')
      | _,        _        => None
      end
  | ECase e' p e1 e2 =>
      match inv_convert_exp e', inv_convert_exp e1, inv_convert_exp e2 with
      | Some e'', Some e1', Some e2' => Some (ESyn.ECase e'' p e1' e2')
      | _,        _,        _        => None
      end
  | ECons e1 e2 =>
      match inv_convert_exp e1, inv_convert_exp e2 with
      | Some e1', Some e2' => Some (ESyn.ECons e1' e2')
      | _,        _        => None
      end
  | EBIF f args =>
      match inv_convert_exp f, mapM inv_convert_exp args with
      | Some f', Some args' => Some (ESyn.EBIF f' args')
      | _,       _          => None
      end
  | EReceive _  => None   (* no counterpart in Env syntax *)
  end.

(**
  Partial inverse of [convert_frame].

  The saved environment [Γ] that was baked into each frame's sub-expressions
  during [convert_frame] cannot be recovered from the converted Sub frame
  alone (it was folded in via [convert_env Γ] / [up_subst (convert_env Γ)]).
  Consequently, the result always carries an empty saved environment [[]].

  Returns [None] if any sub-expression in the frame falls outside the image
  of [convert_exp] — which happens exactly when [up_subst (convert_env Γ)]
  leaves a free [VVar 0] in the body (e.g., in [FLet] frames with non-empty Γ).
*)
Definition inv_convert_frame (f : Frame) : option ESem.Frame :=
  match f with
  | FApp1 args =>
      match mapM inv_convert_exp args with
      | Some args' => Some (ESem.FApp1 args' [])
      | None       => None
      end
  | FApp2 v vl args =>
      match inv_convert_val v,
            mapM inv_convert_val vl,
            mapM inv_convert_exp args with
      | Some v', Some vl', Some args' =>
          Some (ESem.FApp2 v' vl' args' [])
      | _, _, _ => None
      end
  | FLet e2 =>
      match inv_convert_exp e2 with
      | Some e2' => Some (ESem.FLet e2' [])
      | None     => None
      end
  | FCase p e2 e3 =>
      match inv_convert_exp e2, inv_convert_exp e3 with
      | Some e2', Some e3' => Some (ESem.FCase p e2' e3' [])
      | _, _               => None
      end
  | FCons1 e1 =>
      match inv_convert_exp e1 with
      | Some e1' => Some (ESem.FCons1 e1' [])
      | None     => None
      end
  | FCons2 v2 =>
      match inv_convert_val v2 with
      | Some v2' => Some (ESem.FCons2 v2' [])
      | None     => None
      end
  | FBIF1 args =>
      match mapM inv_convert_exp args with
      | Some args' => Some (ESem.FBIF1 args' [])
      | None       => None
      end
  | FBIF2 v vl args =>
      match inv_convert_val v,
            mapM inv_convert_val vl,
            mapM inv_convert_exp args with
      | Some v', Some vl', Some args' =>
          Some (ESem.FBIF2 v' vl' args' [])
      | _, _, _ => None
      end
  end.

(** Lift [inv_convert_frame] pointwise over a full frame stack. *)
Definition inv_convert_framestack (Fs : FrameStack) : option ESem.FrameStack :=
  mapM inv_convert_frame Fs.
(* 
Open Scope env_scope.
Lemma inv_correct :
  (forall e, EXPCLOSED e -> inv_convert_exp (convert_exp e) = Some e) /\
  (forall e, NVALCLOSED e -> inv_convert_exp (convert_nv e) = Some (ESyn.EExp e)) /\
  (forall e, VALCLOSED e -> inv_convert_val (convert_val e) = Some e).
Proof.
  apply Env_Exp_full_ind with
    (Q := Forall (fun e => EXPCLOSED e -> inv_convert_exp (convert_exp e) = Some e))
    (R := Forall (fun e => VALCLOSED e -> inv_convert_val (convert_val e) = Some e)); simpl; intros; try reflexivity.
  * inv H0. by apply H.
  * inv H0. apply H in H2. by rewrite H2.
  * rewrite H.
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  *
Qed. *)


Open Scope env_scope.

Ltac invSome :=
match goal with
| [H : Some _ = Some _ |- _] => inv H
| [H : Some _ = None |- _] => inv H
| [H : None = Some _ |- _] => inv H
| [H : (_, _) = (_, _) |- _] => inv H
end.

Ltac rewrite_cases :=
  repeat match goal with
  | [H : ?x = Some ?y |- context[?x]] => rewrite H
  | [H : ?x = None |- context[?x]] => rewrite H
  end.
 
(** [mapM] distributes over append for the [option] monad. *)
Lemma mapM_app {A B} (f : A → option B) l1 l2 l1' l2' :
  mapM f l1 = Some l1' →
  mapM f l2 = Some l2' →
  mapM f (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  revert l1'. induction l1; intros; cbn in *.
  - inv H. assumption.
  - destruct (f a); [| discriminate].
    destruct (mapM f l1); [| discriminate].
    inv H.
    specialize (IHl1 _ eq_refl H0).
    rewrite IHl1. reflexivity.
Qed.

(*
Lemma inv_convert_exp_val_inv v e' :
  inv_convert_exp (VVal v) = Some e' ->
  ∃ v', inv_convert_val v = Some v' /\ e' = ESyn.VVal v'.
Proof.
  cbn. destruct (inv_convert_val v) eqn:Hv; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_exp_nv_inv nv e' :
  inv_convert_exp (EExp nv) = Some e' ->
  ∃ nv', inv_convert_nv nv = Some nv' /\ e' = ESyn.EExp nv'.
Proof.
  cbn. destruct (inv_convert_nv nv) eqn:Hnv; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_framestack_cons_inv f Fs Fs' :
  inv_convert_framestack (f :: Fs) = Some Fs' ->
  ∃ f' Fs'', inv_convert_frame f = Some f' /\ inv_convert_framestack Fs = Some Fs'' /\ Fs' = f' :: Fs''.
Proof.
  cbn [inv_convert_framestack].
  destruct (inv_convert_frame f) eqn:Hf; [| discriminate].
  destruct (mapM inv_convert_frame Fs) eqn:HFs; [| discriminate].
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_frame_app1_inv args f :
  inv_convert_frame (FApp1 args) = Some f ->
  ∃ args', mapM inv_convert_exp args = Some args' /\ f = ESem.FApp1 args' [].
Proof.
  cbn [inv_convert_frame].
  destruct (mapM inv_convert_exp args) eqn:Hargs; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_frame_app2_inv v vl args f :
  inv_convert_frame (FApp2 v vl args) = Some f ->
  ∃ v' vl' args',
    inv_convert_val v = Some v' /\
    mapM inv_convert_val vl = Some vl' /\
    mapM inv_convert_exp args = Some args' /\
    f = ESem.FApp2 v' vl' args' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_val v) eqn:Hv; [| discriminate].
  destruct (mapM inv_convert_val vl) eqn:Hvl; [| discriminate].
  destruct (mapM inv_convert_exp args) eqn:Hargs; cbn; try congruence.
  intros H. inv H. eauto 10.
Qed.

Lemma inv_convert_frame_bif1_inv args f :
  inv_convert_frame (FBIF1 args) = Some f ->
  ∃ args', mapM inv_convert_exp args = Some args' /\ f = ESem.FBIF1 args' [].
Proof.
  cbn [inv_convert_frame].
  destruct (mapM inv_convert_exp args) eqn:Hargs; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_frame_bif2_inv v vl args f :
  inv_convert_frame (FBIF2 v vl args) = Some f ->
  ∃ v' vl' args',
    inv_convert_val v = Some v' /\
    mapM inv_convert_val vl = Some vl' /\
    mapM inv_convert_exp args = Some args' /\
    f = ESem.FBIF2 v' vl' args' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_val v) eqn:Hv; [| discriminate].
  destruct (mapM inv_convert_val vl) eqn:Hvl; [| discriminate].
  destruct (mapM inv_convert_exp args) eqn:Hargs; cbn; try congruence.
  intros H. inv H. eauto 10.
Qed.

Lemma inv_convert_frame_let_inv e2 f :
  inv_convert_frame (FLet e2) = Some f ->
  ∃ e2', inv_convert_exp e2 = Some e2' /\ f = ESem.FLet e2' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_exp e2) eqn:He2; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_frame_case_inv p e2 e3 f :
  inv_convert_frame (FCase p e2 e3) = Some f ->
  ∃ e2' e3',
    inv_convert_exp e2 = Some e2' /\
    inv_convert_exp e3 = Some e3' /\
    f = ESem.FCase p e2' e3' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_exp e2) eqn:He2; [| discriminate].
  destruct (inv_convert_exp e3) eqn:He3; cbn; try congruence.
  intros H. inv H. eauto 10.
Qed.

Lemma inv_convert_frame_cons1_inv e1 f :
  inv_convert_frame (FCons1 e1) = Some f ->
  ∃ e1', inv_convert_exp e1 = Some e1' /\ f = ESem.FCons1 e1' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_exp e1) eqn:He1; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma inv_convert_frame_cons2_inv v2 f :
  inv_convert_frame (FCons2 v2) = Some f ->
  ∃ v2', inv_convert_val v2 = Some v2' /\ f = ESem.FCons2 v2' [].
Proof.
  cbn [inv_convert_frame].
  destruct (inv_convert_val v2) eqn:Hv2; cbn; try congruence.
  intros H. inv H. eauto.
Qed.

Lemma mapM_cons_inv {A B} (f : A → option B) x xs ys :
  mapM f (x :: xs) = Some ys ->
  ∃ y ys', f x = Some y /\ mapM f xs = Some ys' /\ ys = y :: ys'.
Proof.
  cbn [mapM].
  destruct (f x) eqn:Hx; [| discriminate].
  destruct (mapM f xs) eqn:Hxs; cbn; try congruence.
  intros H. inv H. eauto.
Qed. *)


Lemma inv_convert_exp_subst_id e e' σ :
  inv_convert_exp e = Some e' → e.[σ] = e.
Proof.
Admitted.

(* TODO Basics.v *)
Lemma mapM_app_eq {A B} :
  forall (f : A -> option B) (l1 l2 : list A),
    mapM f (l1 ++ l2) = match mapM f l1 with
                        | Some l1' => match mapM f l2 with
                                      | Some l2' => Some (l1' ++ l2')
                                      | None => None
                                      end
                        | None => None
                        end.
Proof.
  induction l1; intros; simpl.
  by case_match.
  unfold mbind, option_bind.
  destruct (f a) eqn:P. 2: reflexivity.
  rewrite IHl1. clear IHl1.
  destruct mapM; try destruct mapM; simpl.
  all: reflexivity.
Qed.

Lemma match_pattern_inv_convert_Some p v v_s l :
  inv_convert_val v = Some v_s →
  match_pattern p v = Some l →
  ESyn.match_pattern p v_s = mapM inv_convert_val l /\ is_Some (mapM inv_convert_val l).
Proof.
  revert l v_s v. induction p; intros * Hinv Hmatch.
  all: destruct v; simpl in *; try invSome; (try split; [try reflexivity | try by eexists]).
  * case_match; by invSome.
  * case_match; by invSome.
  * case_match; by invSome.
  * case_match; by invSome.
  * case_match; invSome.
    cbn. rewrite H. reflexivity.
  * case_match; invSome. cbn. by rewrite H.
  * case_match; try invSome. case_match; try invSome.
    cbn. by rewrite H, H0.
  * case_match; try invSome. case_match; try invSome. cbn.
    by rewrite H, H0.
  * case_match; try invSome. case_match; try invSome.
    case_match; try invSome. case_match; try invSome.
    specialize (IHp1 _ _ _ H1 H) as [IHp1 IHS1].
    specialize (IHp2 _ _ _ H2 H0) as [IHp2 IHS2].
    rewrite IHp1, IHp2.
    by rewrite mapM_app_eq.
  * case_match; try invSome. case_match; try invSome.
    case_match; try invSome. case_match; try invSome.
    specialize (IHp1 _ _ _ H1 H) as [IHp1 IHS1].
    specialize (IHp2 _ _ _ H2 H0) as [IHp2 IHS2].
    destruct IHS1, IHS2; subst.
    rewrite mapM_app_eq. rewrite H3, H4. by eexists.
Qed.

Lemma match_pattern_inv_convert_None p v v_s :
  inv_convert_val v = Some v_s →
  match_pattern p v = None →
  ESyn.match_pattern p v_s = None.
Proof.
  revert v_s v. induction p; intros * Hinv Hmatch.
  all: destruct v; simpl in *; try invSome; try reflexivity.
  all: case_match; try invSome; try reflexivity.
  * case_match; by invSome.
  * case_match; by invSome.
  * case_match; by invSome.
  * case_match; try invSome. case_match; try invSome. case_match; try invSome.
    erewrite IHp2; try eassumption. by case_match.
  * case_match; try invSome. case_match; try invSome.
    erewrite IHp1; try eassumption. reflexivity.
Qed.

Lemma sub_to_env Fs Fs' e e' Fs_start e_start :
  ⟨Fs, e⟩ --> ⟨Fs', e'⟩ →
  inv_convert_framestack Fs = Some Fs_start →
  inv_convert_exp e = Some e_start →
  ∀ Γ, Γ = [] →
  ∃ Γ' Fs_fin e_fin,
    ⟨Γ, Fs_start, e_start⟩ -->
    ⟨Γ', Fs_fin, e_fin⟩ ∧
    inv_convert_framestack Fs' = Some Fs_fin ∧
    inv_convert_exp e' = Some e_fin.
Proof.
  intros Hstep HFs He Γ HΓ. subst Γ.
  inv Hstep;
  cbn [inv_convert_framestack inv_convert_frame
       inv_convert_exp inv_convert_nv inv_convert_val] in *;
  repeat case_match; cbn in *; try congruence; repeat invSome.

  (* Case 1: red_app_start *)
  - destruct (inv_convert_exp e') eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_exp tl) eqn:P2; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P3; simpl in *; try congruence.
    destruct (mapM inv_convert_frame xs) eqn:P4; simpl in *; try congruence.
    unfold mret, option_ret in HFs.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_app.
    + split; reflexivity.

  (* Case 2: red_app_fin *)
  - destruct (inv_convert_exp e0) eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret in HFs.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_app0. cbn. reflexivity.
    + split.
      * exact P2.
      * rewrite (inv_convert_exp_subst_id _ _ _ P1). exact P1.

  (* Case 3: app2_step *)
  - destruct (inv_convert_val v') eqn:P1; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P2; simpl in *; try congruence.
    destruct (mapM inv_convert_val vs) eqn:P3; simpl in *; try congruence.
    destruct (inv_convert_exp e') eqn:P4; simpl in *; try congruence.
    destruct (mapM inv_convert_exp tl) eqn:P5; simpl in *; try congruence.
    destruct (mapM inv_convert_frame xs) eqn:P6; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    assert (mapM inv_convert_val [v'] = Some [v0]) as R0. {
      cbn. by rewrite P1.
    }
    epose proof (R := mapM_app _ _ _ _ _ P3 R0).
    do 3 eexists. setoid_rewrite R. split.
    + apply ESem.step_app_params.
    + split; reflexivity.

  (* Case 4: red_app2 *)
  - destruct (inv_convert_exp e0) eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_val vs) eqn:P2; simpl in *; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P3; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P4; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_app_params.
      cbn.
      rewrite length_app. rewrite Nat.add_comm. cbn.
      pose proof (length_mapM _ _ _ P2) as Hlen.
      rewrite Hlen. rewrite Nat.eqb_refl. reflexivity.
    + split.
      * exact P3.
      * rewrite (inv_convert_exp_subst_id _ _ _ P1). exact P1.

  (* Case 5: red_bif_start *)
  - destruct (inv_convert_exp e') eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_exp params) eqn:P2; simpl in *; try congruence.
    destruct (mapM inv_convert_frame fs) eqn:P3; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P4; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_bif.
    + split; reflexivity.

  (* Case 6: red_bif_step *)
  - destruct (inv_convert_val v) eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_val vals) eqn:P2; simpl in *; try congruence.
    destruct (inv_convert_exp e') eqn:P3; simpl in *; try congruence.
    destruct (mapM inv_convert_exp params) eqn:P4; simpl in *; try congruence.
    destruct (mapM inv_convert_frame fs) eqn:P5; simpl in *; try congruence.
    destruct (inv_convert_val v') eqn:P6; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + constructor.
    + split; try reflexivity.
      assert (mapM inv_convert_val [v'] = Some [v1]) as R0. {
      cbn. by rewrite P6.
    }
    epose proof (R := mapM_app _ _ _ _ _ P2 R0).
    setoid_rewrite R. reflexivity.

  (* Case 7: red_let *)
  - destruct (inv_convert_exp e2) eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P2; simpl in *; try congruence.
    destruct (inv_convert_val val) eqn:P3; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + constructor.
    + split.
      ** assumption.
      ** rewrite (inv_convert_exp_subst_id _ _ _ P1). exact P1. 

  (* Case 8: red_case_true *)
  - destruct (inv_convert_exp e2) eqn:P1; simpl in *; try congruence.
    destruct (inv_convert_exp e3) eqn:P2; simpl in *; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P3; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P4; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    pose proof match_pattern_inv_convert_Some _ _ _ _ P4 H as [MP [ll S]].
    rewrite S in MP.
    do 3 eexists. split.
    + constructor.
      exact MP.
    + split.
      ** assumption.
      ** rewrite (inv_convert_exp_subst_id _ _ _ P1). exact P1.

  (* Case 9: red_case_false *)
  - destruct (inv_convert_exp e2) eqn:P1; simpl in *; try congruence.
    destruct (inv_convert_exp e') eqn:P2; simpl in *; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P3; simpl in *; try congruence.
    destruct (inv_convert_val v) eqn:P4; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    pose proof (match_pattern_inv_convert_None _ _ _ P4 H) as MP.
    do 3 eexists. split.
    + eapply ESem.red_case_false.
      exact MP.
    + split; [ eassumption | reflexivity ].

  (* Case 10: red_cons1 *)
  - destruct (inv_convert_exp e') eqn:P1; simpl in *; try congruence.
    destruct (mapM inv_convert_frame xs) eqn:P2; simpl in *; try congruence.
    destruct (inv_convert_val v2) eqn:P3; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_cons1.
    + split; reflexivity.

  (* Case 11: red_cons2 *)
  - destruct (inv_convert_val v2) eqn:P1; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + apply ESem.red_cons2.
    + split.
      * exact P2.
      * reflexivity.

  (* Case 12: red_plus *)
  - destruct (inv_convert_val v2) eqn:P1; try congruence.
    destruct (mapM inv_convert_frame Fs') eqn:P2; simpl in *; try congruence.
  - destruct (mapM inv_convert_frame Fs') eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret in *.
    invSome.
    do 3 eexists. split.
    + constructor. reflexivity.
    + split.
      * exact P2.
      * reflexivity.

  (* Case 13: step_let *)
  - destruct (inv_convert_exp e2) eqn:P1; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.step_let.
    + split.
      * cbn. by setoid_rewrite HFs.
      * reflexivity.

  (* Case 14: step_app *)
  - destruct (mapM inv_convert_exp el) eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.step_app.
    + split.
      * cbn. by setoid_rewrite HFs.
      * reflexivity.

  (* Case 15: step_bif *)
  - destruct (mapM inv_convert_exp params) eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.step_bif.
    + split.
      * cbn. by setoid_rewrite HFs.
      * reflexivity.

  (* Case 16: step_case *)
  - destruct (inv_convert_exp e') eqn:P1; simpl in *; try congruence.
    destruct (inv_convert_exp e2) eqn:P2; simpl in *; try congruence.
    destruct (inv_convert_exp e3) eqn:P3; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.step_case.
    + split.
      * cbn. by setoid_rewrite HFs.
      * reflexivity.

  (* Case 17: step_cons *)
  - destruct (inv_convert_exp e1) eqn:P1; simpl in *; try congruence.
    destruct (inv_convert_exp e') eqn:P2; simpl in *; try congruence.
    unfold mret, option_ret, mbind, option_bind in *.
    cbn in *; try congruence.
    invSome.
    do 3 eexists. split.
    + apply ESem.step_cons.
    + split.
      * cbn. by setoid_rewrite HFs.
      * reflexivity.
Qed.
