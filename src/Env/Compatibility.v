(**
  This file records the compatibility statements for CIU and CIU_open in the
  environment-based semantics.

  The statements mirror the role played by the compatibility lemmas for logical
  relations in [src/Compatibility.v], but are adapted to the env syntax and the
  concrete-environment form of [Env.CIU].
 *)

From CoreErlang Require Export Env.CIU.

Import ListNotations.

Inductive cons1_frame_rel (Γ : Env) (e1 e1' : Exp) : FrameStack -> FrameStack -> Prop :=
| cons1_here Fs :
    cons1_frame_rel Γ e1 e1' (FCons1 e1 Γ :: Fs) (FCons1 e1' Γ :: Fs)
| cons1_skip f Fs Fs' :
    cons1_frame_rel Γ e1 e1' Fs Fs' ->
    cons1_frame_rel Γ e1 e1' (f :: Fs) (f :: Fs').

Theorem CIU_Var_compat_closed :
  forall Γ n,
    ENVCLOSED Γ ->
    n < length Γ ->
    CIU Γ (EVar n) (EVar n).
Proof.
  intros Γ n HΓ Hn.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Var_compat :
  forall Γ n,
    n < Γ ->
    CIU_open Γ (EVar n) (EVar n).
Proof.
  intros Γ n Hn Γ' Hlen Hclosed.
  apply CIU_Var_compat_closed.
  - exact Hclosed.
  - lia.
Qed.

Theorem CIU_Lit_compat_closed :
  forall Γ l,
    ENVCLOSED Γ ->
    CIU Γ (˝ (VLit l)) (˝ (VLit l)).
Proof.
  intros Γ l HΓ.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Lit_compat :
  forall Γ l,
    CIU_open Γ (˝ (VLit l)) (˝ (VLit l)).
Proof.
  intros Γ l Γ' Hlen Hclosed.
  apply CIU_Lit_compat_closed.
  exact Hclosed.
Qed.

(* Theorem CIU_Pid_compat_closed :
  forall Γ p,
    CIU Γ (˝ (VPid p)) (˝ (VPid p)).
Proof.
Admitted.

Theorem CIU_Pid_compat :
  forall Γ p,
    CIU_open Γ (˝ (VPid p)) (˝ (VPid p)).
Proof.
Admitted. *)

Theorem CIU_Nil_compat_closed :
  forall Γ,
    ENVCLOSED Γ ->
    CIU Γ (˝ VNil) (˝ VNil).
Proof.
  intros Γ HΓ.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Nil_compat :
  forall Γ,
    CIU_open Γ (˝ VNil) (˝ VNil).
Proof.
  intros Γ Γ' Hlen Hclosed.
  apply CIU_Nil_compat_closed.
  exact Hclosed.
Qed.

Theorem CIU_Cons_compat_closed :
  forall Γ e1 e1' e2 e2',
    CIU Γ e1 e1' ->
    CIU Γ e2 e2' ->
    CIU Γ (ECons e1 e2) (ECons e1' e2').
Proof.
  intros * [H1Γ [H1_1 [H1_2 HD1]]] [H2Γ [H2_1 [H2_2 HD2]]].
  repeat split.
  * assumption.
  * by do 2 constructor.
  * by do 2 constructor.
  * intros * HF D. destruct D as [k0 D]. inv D. apply ex_intro with (x := k) in H4.
    eapply HD2 in H4. 2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct H4 as [i D].
    eapply term_eval_empty in D as D'; eauto.
    2: by apply exp_to_any.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct D' as [v [l [Γ' [Hv D']]]].
    eapply frame_indep_core in D' as D''.
    eapply terminates_step_any_2 in D. 2: exact D''. clear D''. inv D.
    apply ex_intro with (x := k0)in H1. eapply HD1 in H1.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct H1 as [j D].
    eapply term_eval_empty in D as D'''; eauto.
    2: by apply exp_to_any.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct D''' as [v2 [l2 [Γ'2 [Hv2 D'2]]]].
    eapply frame_indep_core in D'2 as D''2.
    eapply terminates_step_any_2 in D. 2: exact D''2. clear D''2.
    inv D.
    eexists. constructor.
    eapply step_term_term_plus. eapply frame_indep_core in D'. exact D'.
    constructor.
    eapply step_term_term_plus. eapply frame_indep_core in D'2. exact D'2.
    constructor.
    exact H1.
Qed.

Theorem CIU_Cons_compat :
  forall Γ e1 e1' e2 e2',
    CIU_open Γ e1 e1' ->
    CIU_open Γ e2 e2' ->
    CIU_open Γ (ECons e1 e2) (ECons e1' e2').
Proof.
Admitted.

Theorem CIU_Fun_compat_closed :
  forall Γ vl b b',
    CIU_open (S vl + length Γ) b b' ->
    CIU Γ (EFun vl b) (EFun vl b').
Proof.
Admitted.

Theorem CIU_Fun_compat :
  forall Γ vl b b',
    CIU_open (S vl + Γ) b b' ->
    CIU_open Γ (EFun vl b) (EFun vl b').
Proof.
Admitted.

Theorem CIU_Let_compat_closed :
  forall Γ e1 e1' e2 e2',
    CIU Γ e1 e1' ->
    CIU_open (S (length Γ)) e2 e2' ->
    CIU Γ (ELet e1 e2) (ELet e1' e2').
Proof.
Admitted.

Theorem CIU_Let_compat :
  forall Γ e1 e1' e2 e2',
    CIU_open Γ e1 e1' ->
    CIU_open (S Γ) e2 e2' ->
    CIU_open Γ (ELet e1 e2) (ELet e1' e2').
Proof.
Admitted.

Theorem CIU_App_compat_closed :
  forall Γ f1 f2 vals1 vals2,
    Forall (fun e => EXP length Γ ⊢ e) vals1 ->
    Forall (fun e => EXP length Γ ⊢ e) vals2 ->
    EXP length Γ ⊢ f1 ->
    EXP length Γ ⊢ f2 ->
    CIU Γ f1 f2 ->
    list_biforall (CIU Γ) vals1 vals2 ->
    CIU Γ (EApp f1 vals1) (EApp f2 vals2).
Proof.
Admitted.

Theorem CIU_App_compat :
  forall Γ f1 f2 vals1 vals2,
    Forall (fun e => EXP Γ ⊢ e) vals1 ->
    Forall (fun e => EXP Γ ⊢ e) vals2 ->
    EXP Γ ⊢ f1 ->
    EXP Γ ⊢ f2 ->
    CIU_open Γ f1 f2 ->
    list_biforall (CIU_open Γ) vals1 vals2 ->
    CIU_open Γ (EApp f1 vals1) (EApp f2 vals2).
Proof.
Admitted.

Theorem CIU_Case_compat_closed :
  forall Γ e1 e1' e2 e2' e3 e3' p,
    CIU Γ e1 e1' ->
    CIU_open (pat_vars p + length Γ) e2 e2' ->
    CIU Γ e3 e3' ->
    CIU Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
Admitted.

Theorem CIU_Case_compat :
  forall Γ e1 e1' e2 e2' e3 e3' p,
    CIU_open Γ e1 e1' ->
    CIU_open (pat_vars p + Γ) e2 e2' ->
    CIU_open Γ e3 e3' ->
    CIU_open Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
Admitted.

Theorem CIU_BIF_compat_closed :
  forall Γ f1 f2 vals1 vals2,
    Forall (fun e => EXP length Γ ⊢ e) vals1 ->
    Forall (fun e => EXP length Γ ⊢ e) vals2 ->
    EXP length Γ ⊢ f1 ->
    EXP length Γ ⊢ f2 ->
    CIU Γ f1 f2 ->
    list_biforall (CIU Γ) vals1 vals2 ->
    CIU Γ (EBIF f1 vals1) (EBIF f2 vals2).
Proof.
Admitted.

Theorem CIU_BIF_compat :
  forall Γ f1 f2 vals1 vals2,
    Forall (fun e => EXP Γ ⊢ e) vals1 ->
    Forall (fun e => EXP Γ ⊢ e) vals2 ->
    EXP Γ ⊢ f1 ->
    EXP Γ ⊢ f2 ->
    CIU_open Γ f1 f2 ->
    list_biforall (CIU_open Γ) vals1 vals2 ->
    CIU_open Γ (EBIF f1 vals1) (EBIF f2 vals2).
Proof.
Admitted.
