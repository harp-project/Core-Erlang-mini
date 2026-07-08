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
    rewrite subst_comp, subst_extend.
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
    rewrite subst_comp, subst_extend.
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

(** Helper: lift [map f] into [option], failing as soon as [f] fails. *)
Fixpoint map_option {A B} (f : A → option B) (l : list A) : option (list B) :=
  match l with
  | []      => Some []
  | x :: xs =>
      match f x, map_option f xs with
      | Some y, Some ys => Some (y :: ys)
      | _,      _       => None
      end
  end.

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
      match inv_convert_exp f, map_option inv_convert_exp args with
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
      match inv_convert_exp f, map_option inv_convert_exp args with
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
      match map_option inv_convert_exp args with
      | Some args' => Some (ESem.FApp1 args' [])
      | None       => None
      end
  | FApp2 v vl args =>
      match inv_convert_val v,
            map_option inv_convert_val vl,
            map_option inv_convert_exp args with
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
      match map_option inv_convert_exp args with
      | Some args' => Some (ESem.FBIF1 args' [])
      | None       => None
      end
  | FBIF2 v vl args =>
      match inv_convert_val v,
            map_option inv_convert_val vl,
            map_option inv_convert_exp args with
      | Some v', Some vl', Some args' =>
          Some (ESem.FBIF2 v' vl' args' [])
      | _, _, _ => None
      end
  end.

(** Lift [inv_convert_frame] pointwise over a full frame stack. *)
Definition inv_convert_framestack (Fs : FrameStack) : option ESem.FrameStack :=
  map_option inv_convert_frame Fs.
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

(** map_option distributes over append *)
Lemma map_option_app {A B} (f : A → option B) l1 l2 l1' l2' :
  map_option f l1 = Some l1' →
  map_option f l2 = Some l2' →
  map_option f (l1 ++ l2) = Some (l1' ++ l2').
Proof.
  revert l1'. induction l1; intros; cbn in *.
  - inv H. assumption.
  - destruct (f a); [| discriminate].
    destruct (map_option f l1); [| discriminate].
    inv H.
    specialize (IHl1 _ eq_refl H0).
    rewrite IHl1. reflexivity.
Qed.

(** map_option preserves list length *)
Lemma map_option_length {A B} (f : A → option B) l l' :
  map_option f l = Some l' → length l = length l'.
Proof.
  revert l'. induction l; intros; cbn in *.
  - inv H. reflexivity.
  - destruct (f a); [| discriminate].
    destruct (map_option f l); [| discriminate].
    inv H. cbn. f_equal. apply IHl. reflexivity.
Qed.

Lemma inv_convert_exp_subst_id e e' σ :
  inv_convert_exp e = Some e' → e.[σ] = e.
Proof.
Admitted.

Lemma match_pattern_inv_some p v v_s l :
  inv_convert_val v = Some v_s →
  match_pattern p v = Some l →
  ∃ l_s, ESyn.match_pattern p v_s = Some l_s.
Proof.
Admitted.

Lemma match_pattern_inv_none p v v_s :
  inv_convert_val v = Some v_s →
  match_pattern p v = None →
  ESyn.match_pattern p v_s = None.
Proof.
Admitted.

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
Admitted.
