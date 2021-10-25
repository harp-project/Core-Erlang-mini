Require Export Compatibility.

Import ListNotations.

Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall F, FSCLOSED F -> | F, e1 | ↓ -> | F, e2 | ↓.

Definition CIU_open (Γ : nat) (e1 e2 : Exp) :=
  forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
  CIU (e1.[ξ]) (e2.[ξ]).

Lemma CIU_closed :
  forall e1 e2,
  CIU e1 e2 -> EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.

Lemma CIU_closed_l : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_l : core.

Lemma CIU_closed_r : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_r : core.

Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  unfold CIU_open in H.
  split;
    eapply subst_implies_scope_exp; eauto.
Qed.

Lemma CIU_open_scope_l : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Global Hint Resolve CIU_open_scope_r : core.

Lemma Erel_implies_CIU : forall Γ e1 e2,
  Erel_open Γ e1 e2 ->
  CIU_open Γ e1 e2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split. 2: split.
  - apply -> (subst_preserves_scope_exp); eauto.
  - apply -> (subst_preserves_scope_exp); eauto.
  - unfold Erel_open, Erel, exp_rel in H. intros. destruct H2.
    specialize (H x ξ ξ (Grel_Fundamental _ _ H0 _)). destruct H, H3.
    eapply H4 in H2; eauto. apply Frel_Fundamental_closed. auto.
Qed.

Lemma Erel_comp_CIU_implies_Erel : forall {Γ e1 e2 e3},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e2 e3 ->
    Erel_open Γ e1 e3.
Proof.
  intros Γ e1 e2 e3 HErel HCIU.
  unfold Erel_open, Erel, exp_rel.
  intros.
  inversion H as [Hξ1 [Hξ2 _]].
  split. 2: split. 1-2: apply -> subst_preserves_scope_exp; eauto.
  intros. eapply HErel in H1; eauto. eapply HCIU in H1; eauto.
Qed.

Lemma CIU_implies_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    Erel_open Γ e1 e2.
Proof.
  intros.
  eapply Erel_comp_CIU_implies_Erel; eauto.
Qed.

Theorem CIU_iff_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 <->
    Erel_open Γ e1 e2.
Proof.
  intuition (auto using CIU_implies_Erel, Erel_implies_CIU).
Qed.

Theorem CIU_eval : forall e1 v,
  EXPCLOSED e1 ->
  ⟨ [], e1 ⟩ -->* v -> CIU e1 v /\ CIU v e1.
Proof.
  intros. split. split. 2: split. auto.
  apply step_any_closedness in H0; auto. 1-2: now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  eapply terminates_step_any. 2: exact H3. eexists. exact H2.

  split. 2: split. 2: auto.
  apply step_any_closedness in H0; auto. 1-2: now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  exists (x + x0).
  eapply term_step_term. exact H3. 2: lia. replace (x + x0 - x0) with x by lia. exact H2.
Qed.

Theorem CIU_list_parts : forall e1 e2 e1' e2',
  VALCLOSED e1 -> VALCLOSED e2 -> VALCLOSED e1' -> VALCLOSED e2' ->
  CIU (ECons e1 e2) (ECons e1' e2')
->
  CIU e1 e1' /\ CIU e2 e2'.
Proof.
  intros. destruct H3 as [? [? ?]].
  split; split.
  1, 3: constructor; auto.
  all: split. 1, 3: constructor; auto.
  * intros. (* smarter pattern matching needed *)
Qed.

Theorem CIU_implies_Vrel :
  forall e1 e2, VALCLOSED e1 -> VALCLOSED e2 -> CIU e1 e2 -> CIU e2 e1 (* for comfort *)
 -> 
  forall n, Vrel n e1 e2.
Proof.
  induction e1; destruct e2; intros; try inversion_is_value; rewrite Vrel_Fix_eq;
    simpl; destruct H1 as [Ecl1 [Ecl2 H1]]; destruct H2 as [Ecl1' [Ecl2' H2]]; try lia.
  * split. 2: split. 1-2: constructor.
    epose proof (H1 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    now apply Z.eqb_eq in H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H2 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * admit.
  * epose proof (H2 [FCase PNil (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H2 [FCase PNil (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase PNil (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase PNil (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * split; constructor; auto.
  * epose proof (H1 [FCase PNil (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PCons PVar PVar) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PCons PVar PVar) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * epose proof (H1 [FCase (PCons PVar PVar) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    inversion H11.
    now apply inf_diverges in H12.
  * split. 2: split. 1-2: auto. inversion H. inversion H0. subst.
    assert (CIU e1_1 e2_1). {
      apply CIU_eval; auto. constructor. auto.
      split. auto. exists 0. constructor.
    specialize (IHe1_1 e2_1 H5 H9).
Qed.
