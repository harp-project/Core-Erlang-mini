From CoreErlang Require Export Env.Semantics.

Reserved Notation "| G , fs , e | k ↓" (at level 80).
Inductive terminates_in_k : Env -> FrameStack -> Exp -> nat -> Prop :=

| term_val v Γ :
  | Γ, [], ˝v | 0 ↓ 

| term_bif0 Γ0 Γ xs v res k :
  eval v [] = Some res ->
  | Γ, xs, res | k ↓ ->
  | Γ0, (FBIF1 [] Γ)::xs, ˝v | S k ↓

| term_bif Γ0 Γ xs e1 l v k :
  | Γ, FBIF2 v [] l Γ :: xs, e1 | k ↓ ->
  | Γ0, (FBIF1 (e1::l) Γ)::xs, ˝v | S k ↓

| term_bif_params Γ0 Γ xs vl e1 el v v0 k :
  | Γ, FBIF2 v (vl ++ [v0]) el Γ :: xs, e1 | k ↓ ->
  | Γ0, (FBIF2 v vl (e1::el) Γ)::xs, ˝v0 | S k ↓

| term_bif_params_done Γ0 Γ xs vl v v0 res k :
  eval v (vl ++ [v0]) = Some res ->
  | Γ, xs, res | k ↓ ->
  | Γ0, (FBIF2 v vl [] Γ)::xs, ˝v0 | S k ↓

| term_app0 Γ0 Γ xs v Γ' res k :
  beta_reduce v [] = Some (Γ', res) ->
  | Γ', xs, res | k ↓ ->
  | Γ0, (FApp1 [] Γ)::xs, ˝v | S k ↓

| term_app Γ0 Γ xs e1 l v k :
  | Γ, FApp2 v [] l Γ :: xs, e1 | k ↓ ->
  | Γ0, (FApp1 (e1::l) Γ)::xs, ˝v | S k ↓

| term_app_params Γ0 Γ xs vl e1 el v v0 k :
  | Γ, FApp2 v (vl ++ [v0]) el Γ :: xs, e1 | k ↓ ->
  | Γ0, (FApp2 v vl (e1::el) Γ)::xs, ˝v0 | S k ↓

| term_app_params_done Γ0 Γ xs vl v v0 Γ' res k :
  beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
  | Γ', xs, res | k ↓ ->
  | Γ0, (FApp2 v vl [] Γ)::xs, ˝v0 | S k ↓

| term_let Γ0 Γ val e2 xs k :
  | val :: Γ, xs, e2 | k ↓ ->
  | Γ0, (FLet e2 Γ)::xs, ˝val | S k ↓

| term_case_true Γ0 Γ e2 e3 v p xs l k :
  match_pattern p v = Some l ->
  | l ++ Γ, xs, e2 | k ↓ ->
  | Γ0, (FCase p e2 e3 Γ)::xs, ˝v | S k ↓

| term_case_false Γ0 Γ e2 e3 p v xs k :
  match_pattern p v = None ->
  | Γ, xs, e3 | k ↓ ->
  | Γ0, (FCase p e2 e3 Γ)::xs, ˝v | S k ↓

| term_cons1 Γ0 Γ xs v2 e1 k :
  | Γ, FCons2 v2 Γ::xs, e1 | k ↓ ->
  | Γ0, FCons1 e1 Γ::xs, ˝v2 | S k ↓

| term_cons2 Γ0 Γ xs v2 v1 k :
  | Γ, xs, VCons v1 v2 | k ↓ ->
  | Γ0, FCons2 v2 Γ::xs, ˝v1 | S k ↓

(** Steps *)
| term_step_let Γ xs e1 e2 k :
  | Γ, (FLet e2 Γ)::xs, e1 | k ↓ ->
  | Γ, xs, ELet e1 e2 | S k ↓
| term_step_app Γ xs e el k :
  | Γ, (FApp1 el Γ)::xs, e | k ↓ ->
  | Γ, xs, EApp e el | S k ↓
| term_step_bif Γ fs name params k :
  | Γ, FBIF1 params Γ :: fs, name | k ↓ ->
  | Γ, fs, EBIF name params | S k ↓
| term_step_case Γ xs e1 p e2 e3 k :
  | Γ, (FCase p e2 e3 Γ)::xs, e1 | k ↓ ->
  | Γ, xs, ECase e1 p e2 e3 | S k ↓
| term_step_cons Γ xs e1 e2 k :
  | Γ, (FCons1 e1 Γ) :: xs, e2 | k ↓ ->
  | Γ, xs, ECons e1 e2 | S k ↓

(** Additional rules to handle environments *)
| term_fun Γ xs vl e k :
  | Γ, xs, VClos Γ vl e | k ↓ ->
  | Γ, xs, EFun vl e | S k ↓

| term_var Γ xs x (val : Val) k :
  Γ !! x = Some val ->
  | Γ, xs, ˝val | k ↓ ->
  | Γ, xs, EVar x | S k ↓
where "| G , fs , e | k ↓" := (terminates_in_k G fs e k) : env_scope.

Definition terminates Γ fs e := exists k, | Γ, fs, e | k ↓.
Notation "| G , fs , e | ↓" := (terminates G fs e) (at level 80) : env_scope.

Definition terminates_sem Γ fs e v :=
  exists k Γ', ⟨Γ, fs, e⟩ -[k]-> ⟨Γ', [], ˝v⟩.

Notation "⟨ Γ , fs , e ⟩ -->* v" := (terminates_sem Γ fs e v) (at level 50) : env_scope.

Theorem termination_semantics :
  forall Γ fs e k, | Γ , fs , e | k ↓ ->
    exists Γ' v, ⟨ Γ , fs , e ⟩ -[k]-> ⟨Γ', [], ˝v⟩.
Proof.
  intros Γ fs e k Hterm.
  induction Hterm.
  - exists Γ, v. constructor.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif0. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_bif_params.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif_params. exact H.
    + exact IH.
  - destruct IHHterm as [Γ'' [v' IH]].
    exists Γ'', v'. eapply step_trans.
    + apply red_app0. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_app.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_app_params.
    + exact IH.
  - destruct IHHterm as [Γ'' [v' IH]].
    exists Γ'', v'. eapply step_trans.
    + apply red_app_params. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_let.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_case_true. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_case_false. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_cons1.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_cons2.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_let.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_app.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_bif.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_case.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_cons.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_fun.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_var. exact H.
    + exact IH.
Qed.

Theorem semantics_termination :
  forall k Γ fs e v Γ', ⟨ Γ , fs , e ⟩ -[k]-> ⟨Γ', [], ˝v ⟩ ->
    | Γ , fs , e | k ↓.
Proof.
  intros k.
  induction k; intros Γ fs e Γ' v Hrt; inv Hrt.
  * constructor.
  * inv H0. all: try by (constructor; eapply IHk; eassumption).
    all: try by (econstructor; [ eassumption | eapply IHk; eassumption]).
Qed.

Corollary terminates_semantics :
  forall Γ fs e, | Γ , fs , e | ↓ ->
    exists v, ⟨ Γ , fs , e ⟩ -->* v.
Proof.
  intros Γ fs e [k Hterm].
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ' [v Hsteps]].
  exists v. exists k, Γ'. exact Hsteps.
Qed.

Corollary semantics_terminates :
  forall Γ fs e v, ⟨ Γ , fs , e ⟩ -->* v ->
    | Γ , fs , e | ↓.
Proof.
  intros Γ fs e v [k [Γ' Hsteps]].
  exists k. eapply semantics_termination. exact Hsteps.
Qed.

Corollary transitive_eval :
  forall k Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
    forall k' Γ'' fs'' e'',
      ⟨ Γ', fs', e' ⟩ -[k']-> ⟨ Γ'', fs'', e'' ⟩ ->
      ⟨ Γ, fs, e ⟩ -[k + k']-> ⟨ Γ'', fs'', e'' ⟩.
Proof.
  intros k Γ fs e Γ' fs' e' Hrt.
  induction Hrt; intros k' Γ1 fs1 e1 Hrt'; simpl.
  - exact Hrt'.
  - econstructor.
    + exact H.
    + eapply IHHrt. exact Hrt'.
Qed.

Corollary terminates_step_any :
  forall Γ fs e,
    | Γ, fs, e | ↓ ->
    forall k Γ' fs' e',
      ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓.
Proof.
  intros Γ fs e Hterm k Γ' fs' e' Hpre.
  assert (Hstep_term :
    forall Γ0 fs0 e0 Γ1 fs1 e1,
      | Γ0, fs0, e0 | ↓ ->
      ⟨ Γ0, fs0, e0 ⟩ --> ⟨ Γ1, fs1, e1 ⟩ ->
      | Γ1, fs1, e1 | ↓).
  {
    intros Γ0 fs0 e0 Γ1 fs1 e1 [n Hn] Hstep.
    destruct (termination_semantics _ _ _ _ Hn) as [Γf [v Hfull]].
    inversion Hfull; subst.
    - inversion Hn; subst. exfalso. eapply value_nostep. exact Hstep.
    - match goal with
        | Hs : ⟨ _, _, _ ⟩ --> ⟨ _, _, _ ⟩,
          Htail : ⟨ _, _, _ ⟩ -[ _ ]-> ⟨ _, _, _ ⟩ |- _ =>
            pose proof (step_determinism _ _ _ _ _ _ Hstep _ _ _ Hs) as [-> [-> ->]];
            eapply semantics_terminates;
            exists k0, Γf;
            exact Htail
      end.
  }
  induction Hpre.
  - exact Hterm.
  - eapply IHHpre.
    eapply Hstep_term; eauto.
Qed.

(**
  For a value plugged into a frame stack, termination is independent of the
  current ambient environment.
 *)
Lemma value_terminates_in_k_env_indep :
  forall k Γ1 Γ2 fs (v : Val),
    | Γ1, fs, ˝v | k ↓ ->
    | Γ2, fs, ˝v | k ↓.
Proof.
  intros k Γ1 Γ2 fs v Hterm.
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ' [w Hsteps]].
  destruct (value_core_env_indep _ _ _ _ _ _ Hsteps Γ2) as [Γ'' Hsteps'].
  eapply semantics_termination. exact Hsteps'.
Qed.

Corollary value_terminates_env_indep :
  forall Γ1 Γ2 fs (v : Val),
    | Γ1, fs, ˝v | ↓ ->
    | Γ2, fs, ˝v | ↓.
Proof.
  intros Γ1 Γ2 fs v [k Hterm].
  exists k. eapply value_terminates_in_k_env_indep. exact Hterm.
Qed.

Corollary value_terminates_sem_env_indep :
  forall Γ1 Γ2 fs (v w : Val),
    ⟨ Γ1, fs, ˝v ⟩ -->* w ->
    ⟨ Γ2, fs, ˝v ⟩ -->* w.
Proof.
  intros Γ1 Γ2 fs v w [k [Γ' Hsteps]].
  destruct (value_core_env_indep _ _ _ _ _ _ Hsteps Γ2) as [Γ'' Hsteps'].
  exists k, Γ''. exact Hsteps'.
Qed.
