From CoreErlang.Env Require Import Semantics.
From CoreErlang Require Import SubstSemantics.

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
  | ESyn.VVar n      => VVar n   (* absent in closed runtime values *)
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

(* ------------------------------------------------------------------ *)
(*  Runtime well-formedness                                            *)
(* ------------------------------------------------------------------ *)

(** A runtime Env value is [wf_val v] when its Sub translation is closed. *)
Definition wf_val (v : ESyn.Val) : Prop := VALCLOSED (convert_val v).

(** An environment [Γ] is [wf_env Γ] when every stored value is closed. *)
Definition wf_env (Γ : ESem.Env) : Prop := Forall wf_val Γ.

(** A frame is [wf_frame f] when the values stored inside it are closed.
    Only [FCons2] currently needs explicit tracking (its [v2] is used as
    a Val in the Sub [red_cons2] rule). *)
Print ESem.Frame.
Definition wf_frame (f : ESem.Frame) : Prop :=
match f with
 | ESem.FApp1 l Γ => wf_env Γ
 | ESem.FBIF1 l Γ => wf_env Γ
 | ESem.FLet e2 Γ => wf_env Γ
 | ESem.FCase p e2 e3 Γ => wf_env Γ
 | ESem.FCons1 e1 Γ => wf_env Γ
 | ESem.FCons2 v2 Γ => wf_env Γ /\ wf_val v2
 | ESem.FApp2 v l el Γ => wf_env Γ /\ wf_val v /\ Forall wf_val l
 | ESem.FBIF2 v l el Γ => wf_env Γ /\ wf_val v /\ Forall wf_val l
end.

Definition wf_framestack (Fs : ESem.FrameStack) : Prop :=
  Forall wf_frame Fs.

(* ------------------------------------------------------------------ *)
(*  Helper lemmas                                                      *)
(* ------------------------------------------------------------------ *)

Lemma wf_env_lookup Γ n v :
  wf_env Γ → Γ !! n = Some v → wf_val v.
Proof.
  intros HΓ Hn. eapply Forall_lookup in HΓ.
  2: exact Hn. assumption.
Qed.

(** A closed Sub value is invariant under any substitution. *)
Lemma wf_val_subst_id v σ :
  wf_val v → (VVal (convert_val v)).[σ] = VVal (convert_val v).
Proof.
  intros Hv. simpl. rewrite closed_ignores_sub_val; auto.
Qed.

(** Looking up variable [n] in the converted environment gives [convert_val] of
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
Qed.

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

(** Applying a substitution to each [convert_val] in a list is a no-op
    when all elements are well-formed (closed). *)
Lemma map_wf_val_subst_id (l : list ESyn.Val) σ :
  Forall wf_val l →
  map (subst_val σ ∘ convert_val) l = map convert_val l.
Proof.
  induction l; intro H; [reflexivity|].
  inv H. cbn. f_equal.
  - exact (closed_ignores_sub_val _ _ H2).
  - exact (IHl H3).
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
  forall Γ Fs e Γ' Fs' e',
  wf_env Γ →
  wf_framestack Fs →
  (forall v, e = ESyn.VVal v → wf_val v) →
  ⟨Γ, Fs, e⟩ --> ⟨Γ', Fs', e'⟩ ->
  exists k,
  ⟨convert_framestack Fs, (convert_exp e).[convert_env Γ]⟩
    -[k]->
  ⟨convert_framestack Fs', (convert_exp e').[convert_env Γ']⟩ /\ k <= 1.
Proof.
  intros * HwfΓ HwfFs Hval D. inv D; cbn.
  * destruct v; simpl in *; try congruence.
    destruct l. 2: congruence.
    case_match. congruence.
    repeat case_match; congruence.
  * exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite 2! (closed_ignores_sub_val (convert_val v)).
    2-3: by apply Hval.
    constructor.
  * exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_app. simpl.
    rewrite 2! (closed_ignores_sub_val (convert_val v0)).
    2-3: by apply Hval.
    constructor.
  * (* red_bif_params: eval v (vl ++ [v0]) = Some res *)
    inv HwfFs. destruct H2 as (HwfΓ' & Hwfv & Hwfvl).
    apply eval_characterize in H as (z1 & z2 & -> & Hvleq & ->).
    destruct vl as [|w [|? ?]]; try discriminate.
    2: { inv Hvleq. apply f_equal with (f := length) in H2.
         rewrite length_app in H2. simpl in H2. lia.
       }
    inv Hwfvl.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    rewrite (closed_ignores_sub_val _ _ Hwfv).
    cbn.
    rewrite (closed_ignores_sub_val _ _ H1).
    simpl in Hvleq. inv Hvleq.
    exists 1. split. 2: lia.
    econstructor. constructor.
    constructor.
  * (* red_app0: beta_reduce v [] = Some (Γ', res) *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
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
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    constructor.
  * (* step_app_params: accumulate evaluated argument *)
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite map_app. simpl.
    rewrite 2! (closed_ignores_sub_val (convert_val v0)).
    2-3: by apply Hval.
    constructor.
  * (* red_app_params: beta_reduce v (vl ++ [v0]) = Some (Γ', res) *)
    inv HwfFs. destruct H2 as (HwfΓ' & Hwfv & Hwfvl).
    destruct v; cbn in H; try discriminate.
    destruct (Nat.eqb_spec (length (vl ++ [v0])) vl0) as [Hn|]; [|discriminate].
    inv H.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    rewrite (closed_ignores_sub_val _ _ Hwfv).
    rewrite (map_wf_val_subst_id _ _ Hwfvl).
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
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite subst_comp, subst_extend.
    constructor.
  * (* red_case_true: pattern matches, extend env with bindings *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
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
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    apply match_pattern_convert_none in H.
    cbn.
    exists 1. split. 2: lia.
    econstructor. apply red_case_false. exact H.
    constructor.
  * (* red_cons1: push second element frame *)
    inv HwfFs.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    constructor.
  * (* red_cons2: build the cons cell *)
    inv HwfFs. destruct H1 as (HwfΓ' & Hwfv2).
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
    rewrite (closed_ignores_sub_val _ _ Hwfv2).
    cbn.
    exists 1. split. 2: lia.
    econstructor. constructor.
    rewrite (closed_ignores_sub_val _ _ (Hval _ eq_refl)).
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
  * (* red_fun: EFun becomes VClos capturing env — requires scoping invariant *)
    exists 0. split. 2: lia.
    rewrite subst_comp.
    rewrite up_comp, upn_comp.
     
  * (* red_var: look up variable in environment *)
    specialize (Hval _ eq_refl).
    inv Hval. lia.
Admitted.
