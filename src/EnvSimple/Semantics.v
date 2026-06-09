From CoreErlang Require Export EnvSimple.Syntax.
Import ListNotations.
Open Scope env_simple_scope.

Definition Env := list Val.

Inductive Frame : Set :=
| FApp1 (l : list Exp) (Γ : Env)
| FBIF1 (l : list Exp) (Γ : Env)
| FLet (e2 : Exp) (Γ : Env)
| FCase (p : Pat) (e2 e3 : Exp) (Γ : Env)
| FCons1 (e1 : Exp) (Γ : Env)
| FCons2 (v2 : Val) (Γ : Env)
| FApp2 (v : Val) (l : list Val) (el : list Exp) (Γ : Env)
| FBIF2 (v : Val) (l : list Val) (el : list Exp) (Γ : Env).

Definition FrameStack := list Frame.

Inductive Runtime : Set :=
| RExp (e : Exp)
| RVal (v : Val).

Definition eval (f : Val) (l : list Val) : option Val :=
  match f with
  | VLit (Atom "+") =>
      match l with
      | [VLit (Int z1); VLit (Int z2)] => Some (VLit (Int (z1 + z2)))
      | _ => None
      end
  | _ => None
  end.

Definition beta_reduce (f : Val) (params : list Val) : option (Env * Exp) :=
  match f with
  | VClos Γ arity body =>
      if Nat.eqb (length params) arity then
        Some ((VClos Γ arity body) :: params ++ Γ, body)
      else None
  | _ => None
  end.

Reserved Notation "⟨ G , fs , t ⟩ --> ⟨ G' , fs' , t' ⟩" (at level 50).
Inductive step : Env -> FrameStack -> Runtime -> Env -> FrameStack -> Runtime -> Prop :=
| red_bif0 Γ0 Γ xs v res :
    eval v [] = Some res ->
    ⟨ Γ0, FBIF1 [] Γ :: xs, RVal v ⟩ --> ⟨ Γ, xs, RVal res ⟩
| red_bif Γ0 Γ xs e1 l v :
    ⟨ Γ0, FBIF1 (e1 :: l) Γ :: xs, RVal v ⟩ --> ⟨ Γ, FBIF2 v [] l Γ :: xs, RExp e1 ⟩
| step_bif_params Γ0 Γ xs vl e1 el v v0 :
    ⟨ Γ0, FBIF2 v vl (e1 :: el) Γ :: xs, RVal v0 ⟩ -->
    ⟨ Γ, FBIF2 v (vl ++ [v0]) el Γ :: xs, RExp e1 ⟩
| red_bif_params Γ0 Γ xs vl v v0 res :
    eval v (vl ++ [v0]) = Some res ->
    ⟨ Γ0, FBIF2 v vl [] Γ :: xs, RVal v0 ⟩ --> ⟨ Γ, xs, RVal res ⟩
| red_app0 Γ0 Γ xs v Γ' res :
    beta_reduce v [] = Some (Γ', res) ->
    ⟨ Γ0, FApp1 [] Γ :: xs, RVal v ⟩ --> ⟨ Γ', xs, RExp res ⟩
| red_app Γ0 Γ xs e1 l v :
    ⟨ Γ0, FApp1 (e1 :: l) Γ :: xs, RVal v ⟩ --> ⟨ Γ, FApp2 v [] l Γ :: xs, RExp e1 ⟩
| step_app_params Γ0 Γ xs vl e1 el v v0 :
    ⟨ Γ0, FApp2 v vl (e1 :: el) Γ :: xs, RVal v0 ⟩ -->
    ⟨ Γ, FApp2 v (vl ++ [v0]) el Γ :: xs, RExp e1 ⟩
| red_app_params Γ0 Γ xs vl v v0 Γ' res :
    beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
    ⟨ Γ0, FApp2 v vl [] Γ :: xs, RVal v0 ⟩ --> ⟨ Γ', xs, RExp res ⟩
| red_let Γ0 Γ val e2 xs :
    ⟨ Γ0, FLet e2 Γ :: xs, RVal val ⟩ --> ⟨ val :: Γ, xs, RExp e2 ⟩
| red_case_true Γ0 Γ e2 e3 v p xs l :
    match_pattern p v = Some l ->
    ⟨ Γ0, FCase p e2 e3 Γ :: xs, RVal v ⟩ --> ⟨ l ++ Γ, xs, RExp e2 ⟩
| red_case_false Γ0 Γ e2 e3 p v xs :
    match_pattern p v = None ->
    ⟨ Γ0, FCase p e2 e3 Γ :: xs, RVal v ⟩ --> ⟨ Γ, xs, RExp e3 ⟩
| red_cons1 Γ0 Γ xs v2 e1 :
    ⟨ Γ0, FCons1 e1 Γ :: xs, RVal v2 ⟩ --> ⟨ Γ, FCons2 v2 Γ :: xs, RExp e1 ⟩
| red_cons2 Γ0 Γ xs v2 v1 :
    ⟨ Γ0, FCons2 v2 Γ :: xs, RVal v1 ⟩ --> ⟨ Γ, xs, RVal (VCons v1 v2) ⟩
| step_let Γ xs e1 e2 :
    ⟨ Γ, xs, RExp (ELet e1 e2) ⟩ --> ⟨ Γ, FLet e2 Γ :: xs, RExp e1 ⟩
| step_app Γ xs e el :
    ⟨ Γ, xs, RExp (EApp e el) ⟩ --> ⟨ Γ, FApp1 el Γ :: xs, RExp e ⟩
| step_bif Γ fs name params :
    ⟨ Γ, fs, RExp (EBIF name params) ⟩ --> ⟨ Γ, FBIF1 params Γ :: fs, RExp name ⟩
| step_case Γ xs e1 p e2 e3 :
    ⟨ Γ, xs, RExp (ECase e1 p e2 e3) ⟩ --> ⟨ Γ, FCase p e2 e3 Γ :: xs, RExp e1 ⟩
| step_cons Γ xs e1 e2 :
    ⟨ Γ, xs, RExp (ECons e1 e2) ⟩ --> ⟨ Γ, FCons1 e1 Γ :: xs, RExp e2 ⟩
| red_fun Γ xs vl e :
    ⟨ Γ, xs, RExp (EFun vl e) ⟩ --> ⟨ Γ, xs, RVal (VClos Γ vl e) ⟩
| red_var Γ xs x val :
    Γ !! x = Some val ->
    ⟨ Γ, xs, RExp (EVar x) ⟩ --> ⟨ Γ, xs, RVal val ⟩
| red_lit Γ xs l :
    ⟨ Γ, xs, RExp (ELit l) ⟩ --> ⟨ Γ, xs, RVal (VLit l) ⟩
| red_pid Γ xs p :
    ⟨ Γ, xs, RExp (EPid p) ⟩ --> ⟨ Γ, xs, RVal (VPid p) ⟩
| red_nil Γ xs :
    ⟨ Γ, xs, RExp ENil ⟩ --> ⟨ Γ, xs, RVal VNil ⟩
where "⟨ G , fs , t ⟩ --> ⟨ G' , fs' , t' ⟩" := (step G fs t G' fs' t') : env_simple_scope.

Reserved Notation "⟨ G , fs , t ⟩ -[ k ]-> ⟨ G' , fs' , t' ⟩" (at level 50).
Inductive step_rt : Env -> FrameStack -> Runtime -> nat -> Env -> FrameStack -> Runtime -> Prop :=
| step_refl Γ fs t :
    ⟨ Γ, fs, t ⟩ -[0]-> ⟨ Γ, fs, t ⟩
| step_trans Γ fs t Γ' fs' t' Γ'' fs'' t'' k :
    ⟨ Γ, fs, t ⟩ --> ⟨ Γ', fs', t' ⟩ ->
    ⟨ Γ', fs', t' ⟩ -[k]-> ⟨ Γ'', fs'', t'' ⟩ ->
    ⟨ Γ, fs, t ⟩ -[S k]-> ⟨ Γ'', fs'', t'' ⟩
where "⟨ G , fs , t ⟩ -[ k ]-> ⟨ G' , fs' , t' ⟩" := (step_rt G fs t k G' fs' t') : env_simple_scope.

Lemma eval_app_partial_core :
  forall exps f e' v Γ Γ0 Fs hds,
    ⟨ Γ0, FApp2 f hds (e' :: exps) Γ :: Fs, RVal v ⟩ -->
    ⟨ Γ, FApp2 f (hds ++ [v]) exps Γ :: Fs, RExp e' ⟩.
Proof.
  intros. constructor.
Qed.

Theorem step_determinism :
  forall Γ fs t Γ' fs' t',
    ⟨ Γ, fs, t ⟩ --> ⟨ Γ', fs', t' ⟩ ->
    forall Γ'' fs'' t'',
      ⟨ Γ, fs, t ⟩ --> ⟨ Γ'', fs'', t'' ⟩ ->
      Γ'' = Γ' /\ fs'' = fs' /\ t'' = t'.
Proof.
  intros * H. inversion H; subst; intros * H2; inversion H2; subst;
    intuition congruence.
Qed.

Theorem frame_indep_step :
  forall Γ fs t Γ' fs' t',
    ⟨ Γ, fs, t ⟩ --> ⟨ Γ', fs', t' ⟩ ->
    forall fs'',
      ⟨ Γ, fs ++ fs'', t ⟩ --> ⟨ Γ', fs' ++ fs'', t' ⟩.
Proof.
  intros Γ fs t Γ' fs' t' Hstep.
  induction Hstep; intros fs0; simpl; econstructor; eauto.
Qed.

Theorem frame_indep_core :
  forall k Γ fs t Γ' fs' t',
    ⟨ Γ, fs, t ⟩ -[k]-> ⟨ Γ', fs', t' ⟩ ->
    forall fs'',
      ⟨ Γ, fs ++ fs'', t ⟩ -[k]-> ⟨ Γ', fs' ++ fs'', t' ⟩.
Proof.
  intros k Γ fs t Γ' fs' t' Hsteps.
  induction Hsteps; intros fs0.
  - simpl. constructor.
  - econstructor.
    + apply frame_indep_step with (fs'' := fs0). exact H.
    + exact (IHHsteps fs0).
Qed.

Lemma value_nostep :
  forall Γ v Γ' fs' t',
    ⟨ Γ, [], RVal v ⟩ --> ⟨ Γ', fs', t' ⟩ -> False.
Proof.
  intros * H. inversion H.
Qed.

Lemma value_step_env_indep :
  forall Γ1 fs v Γ' fs' t',
    ⟨ Γ1, fs, RVal v ⟩ --> ⟨ Γ', fs', t' ⟩ ->
    forall Γ2,
      ⟨ Γ2, fs, RVal v ⟩ --> ⟨ Γ', fs', t' ⟩.
Proof.
  intros Γ1 fs v Γ' fs' t' Hstep Γ2.
  inversion Hstep; subst; econstructor; eauto.
Qed.

Lemma value_core_env_indep :
  forall k Γ1 fs v w Γ',
    ⟨ Γ1, fs, RVal v ⟩ -[k]-> ⟨ Γ', [], RVal w ⟩ ->
    forall Γ2,
      exists Γ'',
        ⟨ Γ2, fs, RVal v ⟩ -[k]-> ⟨ Γ'', [], RVal w ⟩.
Proof.
  intros k Γ1 fs v w Γ' Hsteps Γ2.
  inversion Hsteps; subst.
  - exists Γ2. constructor.
  - eexists. econstructor.
    + eapply value_step_env_indep. exact H.
    + exact H0.
Qed.
