From CoreErlang Require Export Env.Syntax.
Import ListNotations.
Open Scope env_scope.

Definition Env := list Val.

Inductive Frame : Set :=
| FApp1 (l : list Exp) (Γ : Env) (* apply □(e₁, e₂, ..., eₙ) *)
| FBIF1 (l : list Exp) (Γ : Env) (* call □(e₁, e₂, ..., eₙ) *)
| FLet (e2 : Exp) (Γ : Env) (* let v = □ in e2 *)
| FCase (p : Pat) (e2 e3 : Exp) (Γ : Env) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (Γ : Env) (* [e1 | □] *)
| FCons2 (v2 : Val) (Γ : Env) (* [□ | v2] *)

| FApp2 (v : Val) (l : list Val) (el : list Exp) (Γ : Env)
| FBIF2 (v : Val) (l : list Val) (el : list Exp) (Γ : Env).

Definition FrameStack := list Frame.

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


(*

Inductive heat : Env -> Exp -> Frame -> Exp -> Prop :=


Reserved Notation "⟨ F , v ⟩ -->ᶜ ⟨ G , e ⟩" (at level 50).
Inductive cool : Frame -> Val -> Env -> Exp -> Prop :=

| cool_bif0 Γ xs v res:
  eval v [] = Some res ->
  ⟨ Γ , (FBIF1 [])::xs, ˝v ⟩ --> ⟨ Γ, xs , res⟩

| cool_bif Γ xs e1 l v:
  ⟨ Γ , (FBIF1 (e1::l))::xs, ˝v ⟩ --> ⟨ Γ, FBIF2 v [] l :: xs, e1 ⟩

| cool_bif_params Γ xs vl e1 el v v0:
  ⟨ Γ , (FBIF2 v vl (e1::el))::xs, ˝v0 ⟩ --> ⟨ Γ, FBIF2 v (v0 :: vl) el :: xs, e1 ⟩

| cool_bif_params Γ xs vl v v0 res:
  eval v (vl ++ [v0]) = Some res ->
  ⟨ Γ , (FBIF2 v vl [])::xs, ˝v0 ⟩ --> ⟨ Γ, xs, res ⟩

| cool_app0 Γ xs v Γ' res:
  beta_reduce v [] = Some (Γ', res) ->
  ⟨ Γ , (FApp1 [])::xs, ˝v ⟩ --> ⟨ Γ', xs , res⟩

| cool_app Γ xs e1 l v:
  ⟨ Γ , (FApp1 (e1::l))::xs, ˝v ⟩ --> ⟨ Γ, FApp2 v [] l :: xs, e1 ⟩

| step_app_params Γ xs vl e1 el v v0:
  ⟨ Γ , (FApp2 v vl (e1::el))::xs, ˝v0 ⟩ --> ⟨ Γ, FApp2 v (v0 :: vl) el :: xs, e1 ⟩

| cool_app_params Γ xs vl v v0 Γ' res:
  beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
  ⟨ Γ , (FApp2 v vl [])::xs, ˝v0 ⟩ --> ⟨ Γ', xs, res ⟩


| cool_let Γ val e2 xs :
  ⟨ Γ , (FLet e2)::xs, ˝val ⟩ --> ⟨ val :: Γ, xs, e2 ⟩

| cool_case_true Γ e2 e3 v p xs l : 
  match_pattern p v = Some l
->
  ⟨ Γ, (FCase p e2 e3)::xs, ˝v ⟩ --> ⟨ l ++ Γ, xs, e2 ⟩

| cool_case_false Γ e2 e3 p v xs :
  match_pattern p v = None ->
  ⟨ Γ, (FCase p e2 e3)::xs, ˝v ⟩ --> ⟨ Γ, xs, e3 ⟩

| cool_cons1 Γ xs v2 e1 :
  ⟨ Γ, FCons1 e1::xs, ˝v2⟩ --> ⟨Γ,FCons2 v2::xs, e1 ⟩

| cool_cons2 Γ xs v2 v1 :
  ⟨ Γ,FCons2 v2::xs, ˝v1⟩ --> ⟨Γ,xs, VCons v1 v2 ⟩

where "⟨ F , v ⟩ -->ᶜ ⟨ G , e ⟩" := (cool F v G e).

Reserved Notation "⟨ G , e ⟩ -->ˢ v" (at level 50).
Inductive single : Env -> Exp -> Val -> Prop :=
| red_fun Γ xs vl e:
  ⟨Γ, EFun vl e⟩ -->ₛ VClos Γ vl e

| red_var Γ xs x (val : Val) :
  Γ !! x = Some val ->
  ⟨Γ, VVar x⟩ -->ₛ val.
where "⟨ G , e ⟩ -->ₛ v" := single G e v. *)

Reserved Notation "⟨ G , fs , e ⟩ --> ⟨ G' , fs' , e' ⟩" (at level 50).
Inductive step : Env -> FrameStack -> Exp -> Env -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_bif0 Γ0 Γ xs v res:
  eval v [] = Some res ->
  ⟨ Γ0 , (FBIF1 [] Γ)::xs, ˝v ⟩ --> ⟨ Γ, xs , res⟩

| red_bif Γ0 Γ xs e1 l v:
  ⟨ Γ0 , (FBIF1 (e1::l) Γ)::xs, ˝v ⟩ --> ⟨ Γ, FBIF2 v [] l Γ :: xs, e1 ⟩

| step_bif_params Γ0 Γ xs vl e1 el v v0:
  ⟨ Γ0 , (FBIF2 v vl (e1::el) Γ)::xs, ˝v0 ⟩ --> ⟨ Γ, FBIF2 v (vl ++ [v0]) el Γ :: xs, e1 ⟩

| red_bif_params Γ0 Γ xs vl v v0 res:
  eval v (vl ++ [v0]) = Some res ->
  ⟨ Γ0 , (FBIF2 v vl [] Γ)::xs, ˝v0 ⟩ --> ⟨ Γ, xs, res ⟩

| red_app0 Γ0 Γ xs v Γ' res:
  beta_reduce v [] = Some (Γ', res) ->
  ⟨ Γ0 , (FApp1 [] Γ)::xs, ˝v ⟩ --> ⟨ Γ', xs , res⟩

| red_app Γ0 Γ xs e1 l v:
  ⟨ Γ0 , (FApp1 (e1::l) Γ)::xs, ˝v ⟩ --> ⟨ Γ, FApp2 v [] l Γ :: xs, e1 ⟩

| step_app_params Γ0 Γ xs vl e1 el v v0:
  ⟨ Γ0 , (FApp2 v vl (e1::el) Γ)::xs, ˝v0 ⟩ --> ⟨ Γ, FApp2 v (vl ++ [v0]) el Γ :: xs, e1 ⟩

| red_app_params Γ0 Γ xs vl v v0 Γ' res:
  beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
  ⟨ Γ0 , (FApp2 v vl [] Γ)::xs, ˝v0 ⟩ --> ⟨ Γ', xs, res ⟩


| red_let Γ0 Γ val e2 xs :
  ⟨ Γ0 , (FLet e2 Γ)::xs, ˝val ⟩ --> ⟨ val :: Γ, xs, e2 ⟩

| red_case_true Γ0 Γ e2 e3 v p xs l : 
  match_pattern p v = Some l
->
  ⟨ Γ0, (FCase p e2 e3 Γ)::xs, ˝v ⟩ --> ⟨ l ++ Γ, xs, e2 ⟩

| red_case_false Γ0 Γ e2 e3 p v xs :
  match_pattern p v = None ->
  ⟨ Γ0, (FCase p e2 e3 Γ)::xs, ˝v ⟩ --> ⟨ Γ, xs, e3 ⟩

| red_cons1 Γ0 Γ xs v2 e1 :
  ⟨ Γ0, FCons1 e1 Γ::xs, ˝v2⟩ --> ⟨Γ,FCons2 v2 Γ::xs, e1 ⟩

| red_cons2 Γ0 Γ xs v2 v1 :
  ⟨ Γ0,FCons2 v2 Γ::xs, ˝v1⟩ --> ⟨Γ,xs, VCons v1 v2 ⟩

(** Steps *)
| step_let Γ xs e1 e2 : ⟨ Γ,xs, ELet e1 e2 ⟩ --> ⟨ Γ, (FLet e2 Γ)::xs, e1 ⟩
| step_app Γ xs e el: ⟨ Γ,xs, EApp e el ⟩ --> ⟨ Γ,(FApp1 el Γ)::xs, e ⟩
| step_bif Γ fs name params:
  ⟨Γ,fs, EBIF name params⟩ --> ⟨Γ,FBIF1 params Γ :: fs, name⟩
| step_case Γ xs e1 p e2 e3 : ⟨ Γ,xs, ECase e1 p e2 e3⟩ --> ⟨ Γ,(FCase p e2 e3 Γ)::xs, e1⟩
| step_cons Γ xs e1 e2: ⟨ Γ,xs, ECons e1 e2 ⟩ --> ⟨ Γ,(FCons1 e1 Γ) :: xs, e2 ⟩

(** Additional rules to handle environments *)
| red_fun Γ xs vl e:
  ⟨Γ, xs, EFun vl e⟩ --> ⟨Γ, xs, VClos Γ vl e⟩

| red_var Γ xs x (val : Val) :
  Γ !! x = Some val ->
  ⟨Γ, xs, VVar x⟩ --> ⟨Γ, xs, ˝val⟩
where "⟨ G , fs , e ⟩ --> ⟨ G' , fs' , e' ⟩" := (step G fs e G' fs' e') : env_scope.

Reserved Notation "⟨ G , fs , e ⟩ -[ k ]-> ⟨ G' , fs' , e' ⟩" (at level 50).
Inductive step_rt : Env -> FrameStack -> Exp -> nat -> Env -> FrameStack -> Exp -> Prop :=
| step_refl Γ e Fs : ⟨ Γ, Fs, e ⟩ -[ 0 ]-> ⟨ Γ, Fs, e ⟩
| step_trans Γ fs e Γ' fs' e' Γ'' fs'' e'' k:
  ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e'⟩ -> ⟨Γ', fs', e'⟩ -[ k ]-> ⟨Γ'', fs'', e''⟩
->
  ⟨ Γ, fs, e ⟩ -[S k]-> ⟨Γ'', fs'', e''⟩
where "⟨ G , fs , e ⟩ -[ k ]-> ⟨ G' , fs' , e' ⟩" := (step_rt G fs e k G' fs' e') : env_scope.

