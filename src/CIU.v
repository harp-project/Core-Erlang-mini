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
  * intros. assert (FSCLOSED (FCase (PCons PVar PVar) (EVar 0) inf :: F)). {
       constructor; auto. constructor; auto. 2: repeat constructor.
       simpl. do 2 constructor. auto. inversion H8. inversion H8.
     }
     specialize (H5 (FCase (PCons PVar PVar) (EVar 0) inf :: F) H8).
     destruct H7.
     assert (| FCase (PCons PVar PVar) (EVar 0) inf :: F, ECons e1 e2 | ↓). {
       exists (4 + x). apply term_cons.
       constructor; auto. constructor; auto. eapply term_case_true.
       constructor; auto. reflexivity.
       simpl. auto.
     }
     apply H5 in H9. destruct H9.
     inversion H9; subst; try inversion_is_value.
     inversion H14; subst; try inversion_is_value.
     inversion H16; subst; try inversion_is_value.
     inversion H19; subst; try inversion_is_value.
     - simpl in H23. inversion H23. subst. simpl in H24. eexists; eassumption.
     - apply inf_diverges in H24. contradiction.
  * intros. assert (FSCLOSED (FCase (PCons PVar PVar) (EVar 1) inf :: F)). {
       constructor; auto. constructor; auto. 2: repeat constructor.
       simpl. do 2 constructor. auto. inversion H8. inversion H8.
     }
     specialize (H5 (FCase (PCons PVar PVar) (EVar 1) inf :: F) H8).
     destruct H7.
     assert (| FCase (PCons PVar PVar) (EVar 1) inf :: F, ECons e1 e2 | ↓). {
       exists (4 + x). apply term_cons.
       constructor; auto. constructor; auto. eapply term_case_true.
       constructor; auto. reflexivity.
       simpl. auto.
     }
     apply H5 in H9. destruct H9.
     inversion H9; subst; try inversion_is_value.
     inversion H14; subst; try inversion_is_value.
     inversion H16; subst; try inversion_is_value.
     inversion H19; subst; try inversion_is_value.
     - simpl in H23. inversion H23. subst. simpl in H24. eexists; eassumption.
     - apply inf_diverges in H24. contradiction.
Qed.

(* Theorem CIU_implies_Vrel :
  forall e1 e2, VALCLOSED e1 -> VALCLOSED e2 -> CIU e1 e2 -> CIU e2 e1 (* for comfort *)
 -> 
  forall n, Vrel n e1 e2.
Proof.
  induction e1; destruct e2; intros; try inversion_is_value; rewrite Vrel_Fix_eq;
    simpl; destruct H1 as [Ecl1 [Ecl2 H1]]; destruct H2 as [Ecl1' [Ecl2' H2]]; try lia.
  * split. 2: split. 1-2: constructor.
    epose proof (H1 [FCase (PLit l) (ELit 0) inf] _ _).
    destruct H3. inversion H3; subst; try inversion_is_value.
    simpl in H11. break_match_hyp. now apply Z.eqb_eq in Heqb. congruence.
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
  * split. 2: split. 1-2: auto.
    epose proof (H1 (FCase (PLit 0) (ELit 0) (EApp ))).
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
      apply (CIU_list_parts e1_1 e1_2 e2_1 e2_2); auto.
      split. 2: split. 1-2: do 2 constructor; auto.
      intros. destruct H4.
      inversion H4; subst; try inversion_is_value.
      inversion H13; subst; try inversion_is_value.
      inversion H15; subst; try inversion_is_value.
      assert (exists k, | F, VCons e1_1 e1_2 | k ↓). { eexists; eauto. } apply H1 in H7.
      destruct H7. exists (3 + x). constructor; auto. constructor; auto. constructor; auto.
      auto.
   }
   assert (CIU e1_2 e2_2). {
      apply (CIU_list_parts e1_1 e1_2 e2_1 e2_2); auto.
      split. 2: split. 1-2: do 2 constructor; auto.
      intros. destruct H7.
      inversion H7; subst; try inversion_is_value.
      inversion H14; subst; try inversion_is_value.
      inversion H16; subst; try inversion_is_value.
      assert (exists k, | F, VCons e1_1 e1_2 | k ↓). { eexists; eauto. } apply H1 in H8.
      destruct H8. exists (3 + x). constructor; auto. constructor; auto. constructor; auto.
      auto.
   }
   assert (CIU e2_1 e1_1). {
      apply (CIU_list_parts e2_1 e2_2 e1_1 e1_2); auto.
      split. 2: split. 1-2: do 2 constructor; auto.
      intros. destruct H8.
      inversion H8; subst; try inversion_is_value.
      inversion H15; subst; try inversion_is_value.
      inversion H17; subst; try inversion_is_value.
      assert (exists k, | F, VCons e2_1 e2_2 | k ↓). { eexists; eauto. } apply H2 in H11.
      destruct H11. exists (3 + x). constructor; auto. constructor; auto. constructor; auto.
      auto.
   }
   assert (CIU e2_2 e1_2). {
      apply (CIU_list_parts e2_1 e2_2 e1_1 e1_2); auto.
      split. 2: split. 1-2: do 2 constructor; auto.
      intros. destruct H11.
      inversion H11; subst; try inversion_is_value.
      inversion H16; subst; try inversion_is_value.
      inversion H18; subst; try inversion_is_value.
      assert (exists k, | F, VCons e2_1 e2_2 | k ↓). { eexists; eauto. } apply H2 in H12.
      destruct H12. exists (3 + x). constructor; auto. constructor; auto. constructor; auto.
      auto.
   }
   do 2 rewrite <- Vrel_Fix_eq. split.
   - apply IHe1_1; auto.
   - apply IHe1_2; auto.
Unshelve.
  
Qed. *)
