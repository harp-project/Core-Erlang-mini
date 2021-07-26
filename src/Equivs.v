Require Import CTX.
Import ListNotations.

Notation "e1 ≈[ Γ ]≈ e2" := (CTX Γ e1 e2 /\ CTX Γ e2 e1) (at level 70).
Notation "e1 ≈ e2" := (CTX 0 e1 e2 /\ CTX 0 e2 e1) (at level 70).

Corollary let_abs : forall e2 v x,
  EXP 1 ⊢ e2 -> VALCLOSED v ->
  e2.[v/] ≈ ELet x v e2.
Proof.
  intros. split; now apply CIU_iff_CTX, CIU_beta_value.
Qed.

Corollary let_abs_core : forall Γ e2 v x,
  EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
  e2.[v/] ≈[Γ]≈ ELet x v e2.
Proof.
  intros. split; now apply CIU_iff_CTX, CIU_beta_value.
Qed.

Corollary eta_abs : forall {Γ e vl vals},
  VAL Γ ⊢ EFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals ->
  e.[list_subst (EFun vl e :: vals) idsubst] ≈[Γ]≈ EApp (EFun vl e) vals.
Proof.
  intros. split; now eapply CTX_beta_values.
Qed.

Ltac cpb_term :=
match goal with
| [ H : | _, EPlus _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, EApp _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, ELet _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, ELetRec _ _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, EIf _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _ :: _, _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
end.

Ltac term_step :=
match goal with
| [ H : | ?Fs, ?e | _ ↓, H1 : ⟨ ?Fs, ?e ⟩ -[_]-> ⟨_, _⟩ |- _ ] =>
  eapply (terminates_step_any_2 _ _ _ _ H) in H1 as ?P
end.

Theorem plus_comm : forall Γ e1 e2,
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2 ->
  EPlus e1 e2 ≈[Γ]≈ EPlus e2 e1.
Proof.
  assert (forall e1 e2, EXPCLOSED e1 -> EXPCLOSED e2 -> CIU (EPlus e1 e2) (EPlus e2 e1)). {
    split. 2: split. 1-2: constructor; eauto.
    intros. destruct H2. cpb_term.
    apply term_eval_both in H7 as Eval1.
    destruct Eval1 as [v1 [k1 [v_v1 [Eval1_1 Eval1_2]]]]. term_step.
    cpb_term.
    apply term_eval_both in H8 as Eval1. destruct Eval1 as [v2 [k2 [v_v2 [Eval2_1 Eval2_2]]]].
    term_step.
    cpb_term.
    exists (3 + (k2 + (k1 + k3))). constructor.
    
    eapply term_step_term.
    eapply frame_indep_nil in Eval2_1. exact Eval2_1.
    replace (S (S (k2 + (k1 + k3))) - k2) with (S (S (k1 + k3))) by lia.
    
    constructor; auto. 2: lia.
    eapply term_step_term.
    eapply frame_indep_nil in Eval1_1. exact Eval1_1.
    replace (S (k1 + k3) - k1) with (S k3) by lia.
    
    constructor.
    now rewrite Z.add_comm. lia.
  }
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; apply H.
  all: apply -> subst_preserves_scope_exp; eauto.
Qed.

Corollary eval_equiv :
  forall e1 v : Exp, EXPCLOSED e1 -> ⟨ [], e1 ⟩ -->* v
->
  e1 ≈ v.
Proof.
  apply CTX_eval.
Qed.

Theorem let_delay : forall Γ e x e',
  EXP Γ ⊢ e -> EXPCLOSED e' -> | [], e' | ↓ ->
  e ≈[Γ]≈ ELet x e' (rename (fun n => S n) e).
Proof.
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; split;
    [idtac|split|idtac|split]. 2, 4: constructor.
  Search up_subst ">>".
  3, 5: rewrite renaming_is_subst.
  1, 3-4, 7: apply -> subst_preserves_scope_exp; eauto.
  1-2: apply -> subst_preserves_scope_exp; eauto.
  1-2: intro; intros; simpl; lia.
  1-2: rewrite eclosed_ignores_sub; auto.
  * intros. destruct H4, H1.
    apply term_eval in H1. destruct H1, H1, H1.
    eapply frame_indep_nil in H5. assert (e'.[ξ] = e'). { rewrite eclosed_ignores_sub; auto. } rewrite H6 in *.
    exists (S (x3 + S x0)). constructor.
    eapply term_step_term. simpl in H5. exact H5.
    replace (x3 + S x0 - x3) with (S x0) by lia.
    
    constructor; auto. 2: lia.
    rewrite renaming_is_subst, subst_comp, subst_extend, subst_comp.
    replace (ren (fun n : nat => S n) >> inl x2 .:: ξ) with (ξ) by reflexivity. auto.
  * intros. destruct H4. cpb_term.
    apply term_eval_both in H10 as H10'. destruct H10' as [v [k0 [v_v [Eval1 Eval2]]]].
    term_step.
    cpb_term. exists k1.
    rewrite renaming_is_subst, subst_comp, subst_extend, subst_comp in H11.
    exact H11.
Qed.

