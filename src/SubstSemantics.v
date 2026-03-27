(**

  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we describe the frame stack semantics for sequential
  Core Erlang.
*)

Require Export Scoping.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Export Coq.Arith.Wf_nat.
Export PeanoNat.

Import ListNotations.

(** Based on https://github.com/cobbal/ppl-ctx-equiv-coq 
    Frame stack semantics:
*)


Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
(** The semantics of applications and BIFs is tricky. We evaluate the
    main expressions, and then the parameters are split into two lists:
    the first contain the expressions that still need to be evaluated
    while the second contains the already evaluated ones. Thus removing
    and evaluating an element from the first list will append the
    value to the end of the second list. *)
| red_app_start v hd tl xs:
  ⟨ (FApp1 (hd::tl))::xs, VVal v ⟩ --> ⟨ (FApp2 v [] tl)::xs, hd⟩

| red_app_fin xs e :
  ⟨ (FApp1 [])::xs, VVal (VFun 0 e) ⟩ --> ⟨ xs, e.[VFun 0 e/] ⟩

| app2_step v hd tl vs xs v' :
  ⟨ (FApp2 v vs (hd::tl)) :: xs, VVal v' ⟩ --> ⟨ (FApp2 v (vs ++ [v']) tl) :: xs, hd ⟩

| red_app2 vl e vs v xs : 
  vl = S (length vs) ->
  ⟨ (FApp2 (VFun vl e) vs []) :: xs, VVal v ⟩ --> ⟨ xs,  e.[list_subst (VFun vl e :: (vs ++ [v])) idsubst] ⟩

| red_bif_start fs e params v :
  ⟨FBIF1 (e::params) :: fs, VVal v⟩ --> ⟨ FBIF2 v [] params ::fs , e⟩
| red_bif_step fs e v v' params vals :
  ⟨FBIF2 v vals (e :: params) :: fs, VVal v'⟩ -->
  ⟨FBIF2 v (vals ++ [v']) params :: fs, e⟩

| red_let val e2 xs : ⟨ (FLet e2)::xs, VVal val ⟩ --> ⟨ xs, e2.[val/] ⟩

| red_case_true e2 e3 v p xs l : 
  match_pattern p v = Some l
->
  ⟨ (FCase p e2 e3)::xs, VVal v ⟩ --> ⟨ xs, e2.[list_subst l idsubst] ⟩

| red_case_false e2 e3 p v xs :
  match_pattern p v = None ->
  ⟨ (FCase p e2 e3)::xs, VVal v ⟩ --> ⟨ xs, e3 ⟩

| red_cons1 xs v2 e1 :
  ⟨ FCons1 e1::xs, VVal v2⟩ --> ⟨FCons2 v2::xs, e1 ⟩

| red_cons2 xs v2 v1 :
  ⟨ FCons2 v2::xs, VVal v1⟩ --> ⟨xs, VCons v1 v2 ⟩

| red_plus xs i1 i2 :
  ⟨ (FBIF2 (VLit "+"%string) [VLit (Int i1)] []) :: xs, VVal (VLit (Int i2))⟩ --> 
    ⟨xs, VVal (VLit (Z.add i1 i2))⟩

(** Steps *)
| step_let xs e1 e2 : ⟨ xs, ELet e1 e2 ⟩ --> ⟨ (FLet e2)::xs, e1 ⟩
| step_app xs e el: ⟨ xs, EApp e el ⟩ --> ⟨ (FApp1 el)::xs, e ⟩
| step_bif fs name params:
  ⟨fs, EBIF name params⟩ --> ⟨FBIF1 params :: fs, name⟩
| step_case xs e1 p e2 e3 : ⟨ xs, ECase e1 p e2 e3⟩ --> ⟨ (FCase p e2 e3)::xs, e1⟩
| step_cons xs e1 e2: ⟨ xs, ECons e1 e2 ⟩ --> ⟨ (FCons1 e1) :: xs, e2 ⟩
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e') : sub_scope.

Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Exp -> nat -> FrameStack -> Exp -> Prop :=
| step_refl e Fs : ⟨ Fs, e ⟩ -[ 0 ]-> ⟨ Fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e') : sub_scope.

Definition step_any (fs : FrameStack) (e : Exp) (v : Val) : Prop :=
  exists k, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.

Notation "⟨ fs , e ⟩ -->* v" := (step_any fs e v) (at level 50) : sub_scope.

Global Hint Constructors ExpScoped : core.
Global Hint Constructors ValScoped : core.
