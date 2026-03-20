From CoreErlang Require Export Env.Syntax.
Import ListNotations.
Open Scope env_scope.


Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FBIF1 (l : list Exp) (* call □(e₁, e₂, ..., eₙ) *)
| FLet (e2 : Exp) (* let v = □ in e2 *)
| FCase (p : Pat) (e2 e3 : Exp) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (* [e1 | □] *)
| FCons2 (v2 : Val) (* [□ | v2] *)

| FApp2 (v : Val) (l : list Val) (el : list Exp)
| FBIF2 (v : Val) (l : list Val) (el : list Exp).

Definition FrameStack := list Frame.

Definition Environment := list Val.

Definition eval (f : Val) (l : list Val) : option Val :=
match f with
| VLit (Atom "+") =>
  match l with
  | [VLit (Int z1); VLit (Int z2)] => Some (VLit (Int (z1 + z2)))
  | _ => None
  end
| _ => None
end.

Definition beta_reduce (f : Val) (params : list Val) : option (Environment * Exp) :=
match f with
| VClos Γ arity body =>
    if Nat.eqb (length params) arity then
      Some ((VClos Γ arity body) :: params ++ Γ, body)
    else None
| _ => None
end.


Reserved Notation "⟨ G , fs , e ⟩ --> ⟨ G' , fs' , e' ⟩" (at level 50).
Inductive step : Environment -> FrameStack -> Exp -> Environment -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_bif0 Γ xs v res:
  eval v [] = Some res ->
  ⟨ Γ , (FBIF1 [])::xs, ˝v ⟩ --> ⟨ Γ, xs , res⟩

| red_bif Γ xs e1 l v:
  ⟨ Γ , (FBIF1 (e1::l))::xs, ˝v ⟩ --> ⟨ Γ, FBIF2 v [] l :: xs, e1 ⟩

| step_bif_params Γ xs vl e1 el v v0:
  ⟨ Γ , (FBIF2 v vl (e1::el))::xs, ˝v0 ⟩ --> ⟨ Γ, FBIF2 v (v0 :: vl) el :: xs, e1 ⟩

| red_bif_params Γ xs vl v v0 res:
  eval v (vl ++ [v0]) = Some res ->
  ⟨ Γ , (FBIF2 v vl [])::xs, ˝v0 ⟩ --> ⟨ Γ, xs, res ⟩

| red_app0 Γ xs v Γ' res:
  beta_reduce v [] = Some (Γ', res) ->
  ⟨ Γ , (FApp1 [])::xs, ˝v ⟩ --> ⟨ Γ', xs , res⟩

| red_app Γ xs e1 l v:
  ⟨ Γ , (FApp1 (e1::l))::xs, ˝v ⟩ --> ⟨ Γ, FApp2 v [] l :: xs, e1 ⟩

| step_app_params Γ xs vl e1 el v v0:
  ⟨ Γ , (FApp2 v vl (e1::el))::xs, ˝v0 ⟩ --> ⟨ Γ, FApp2 v (v0 :: vl) el :: xs, e1 ⟩

| red_app_params Γ xs vl v v0 Γ' res:
  beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
  ⟨ Γ , (FApp2 v vl [])::xs, ˝v0 ⟩ --> ⟨ Γ', xs, res ⟩


| red_let Γ val e2 xs :
  ⟨ Γ , (FLet e2)::xs, ˝val ⟩ --> ⟨ val :: Γ, xs, e2 ⟩

| red_case_true Γ e2 e3 v p xs l : 
  match_pattern p v = Some l
->
  ⟨ Γ, (FCase p e2 e3)::xs, ˝v ⟩ --> ⟨ l ++ Γ, xs, e2 ⟩

| red_case_false Γ e2 e3 p v xs :
  match_pattern p v = None ->
  ⟨ Γ, (FCase p e2 e3)::xs, ˝v ⟩ --> ⟨ Γ, xs, e3 ⟩

| red_cons1 Γ xs v2 e1 :
  ⟨ Γ, FCons1 e1::xs, ˝v2⟩ --> ⟨Γ,FCons2 v2::xs, e1 ⟩

| red_cons2 Γ xs v2 v1 :
  ⟨ Γ,FCons2 v2::xs, ˝v1⟩ --> ⟨Γ,xs, VCons v1 v2 ⟩

(** Steps *)
| step_let Γ xs e1 e2 : ⟨ Γ,xs, ELet e1 e2 ⟩ --> ⟨ Γ,(FLet e2)::xs, e1 ⟩
| step_app Γ xs e el: ⟨ Γ,xs, EApp e el ⟩ --> ⟨ Γ,(FApp1 el)::xs, e ⟩
| step_bif Γ fs name params:
  ⟨Γ,fs, EBIF name params⟩ --> ⟨Γ,FBIF1 params :: fs, name⟩
| step_case Γ xs e1 p e2 e3 : ⟨ Γ,xs, ECase e1 p e2 e3⟩ --> ⟨ Γ,(FCase p e2 e3)::xs, e1⟩
| step_cons Γ xs e1 e2: ⟨ Γ,xs, ECons e1 e2 ⟩ --> ⟨ Γ,(FCons1 e1) :: xs, e2 ⟩

(** Additional rules to handle environments *)
| red_fun Γ xs vl e:
  ⟨Γ, xs, EFun vl e⟩ --> ⟨Γ, xs, VClos Γ vl e⟩

| red_var Γ xs x (val : Val) :
  Γ !! x = Some val ->
  ⟨Γ, xs, VVar x⟩ --> ⟨Γ, xs, ˝val⟩
where "⟨ G , fs , e ⟩ --> ⟨ G' , fs' , e' ⟩" := (step G fs e G' fs' e').

Reserved Notation "⟨ G , fs , e ⟩ -[ k ]-> ⟨ G' , fs' , e' ⟩" (at level 50).
Inductive step_rt : Environment -> FrameStack -> Exp -> nat -> Environment -> FrameStack -> Exp -> Prop :=
| step_refl Γ e Fs : ⟨ Γ, Fs, e ⟩ -[ 0 ]-> ⟨ Γ, Fs, e ⟩
| step_trans Γ fs e Γ' fs' e' Γ'' fs'' e'' k:
  ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e'⟩ -> ⟨Γ', fs', e'⟩ -[ k ]-> ⟨Γ'', fs'', e''⟩
->
  ⟨ Γ, fs, e ⟩ -[S k]-> ⟨Γ'', fs'', e''⟩
where "⟨ G , fs , e ⟩ -[ k ]-> ⟨ G' , fs' , e' ⟩" := (step_rt G fs e k G' fs' e').

