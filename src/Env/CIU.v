From CoreErlang Require Export Env.Termination
                               Env.ClosedScoping.

Definition CIU (Γ : Env) (e1 e2 : Exp) :=
  ENVCLOSED Γ /\ EXP length Γ ⊢ e1 /\ EXP length Γ ⊢ e2 /\
    forall Fs, FSCLOSED Fs ->
      | Γ, Fs, e1 | ↓ -> | Γ, Fs, e2 | ↓.

Definition CIU_open (n : nat) (e1 e2 : Exp) :=
  forall Γ, length Γ = n -> ENVCLOSED Γ -> CIU Γ e1 e2.

Lemma CIU_scope : forall Γ e1 e2,
    CIU Γ e1 e2 ->
    EXP length Γ ⊢ e1 /\ EXP length Γ ⊢ e2.
Proof.
  intros Γ e1 e2 HCIU.
  unfold CIU in HCIU. intuition.
Qed.

Lemma CIU_scope_l : forall {Γ e1 e2},
    CIU Γ e1 e2 ->
    EXP length Γ ⊢ e1.
Proof.
  intros.
  apply CIU_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_scope_l : core.

Lemma CIU_scope_r : forall {Γ e1 e2},
    CIU Γ e1 e2 ->
    EXP length Γ ⊢ e2.
Proof.
  intros.
  apply CIU_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_scope_r : core.


Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros Γ e1 e2 H.
  unfold CIU_open in H.
  assert (ENVCLOSED (repeat VNil Γ)) as Hclosed.
  {
    clear H e1 e2.
    induction Γ.
    - constructor.
    - simpl. constructor.
      + constructor.
      + exact IHΓ.
  }
  specialize (H (repeat VNil Γ) (repeat_length VNil Γ) Hclosed).
  apply CIU_scope in H.
  rewrite repeat_length in H.
  exact H.
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

Theorem CIU_eval : forall e1 v Γ,
  EXP length Γ ⊢ e1 -> ENVCLOSED Γ ->
  ⟨ Γ, [], e1 ⟩ -->* v ->
    CIU Γ e1 v /\ CIU Γ v e1.
Proof.
  intros e1 v Γ He1 HΓ [k [Γ' D]].
  assert (Hv : VALCLOSED v).
  {
    pose proof D as D'.
    apply scope_preservation_any in D'; try eassumption.
    - destruct D' as [D' _]. simpl in D'. exact D'.
    - by apply exp_to_any.
    - constructor.
  }
  split.
  - unfold CIU. repeat split; try assumption.
    + constructor. exact Hv.
    + intros Fs Hfs Hterm.
      pose proof (frame_indep_core _ _ _ _ _ _ _ D Fs) as DFs.
      simpl in DFs.
      assert (| Γ', Fs, ˝v | ↓).
      { eapply terminates_step_any; eauto. }
      eapply value_terminates_env_indep; eauto.
  - unfold CIU. repeat split; try assumption.
    + constructor. exact Hv.
    + intros Fs Hfs Hterm.
      pose proof (frame_indep_core _ _ _ _ _ _ _ D Fs) as DFs.
      simpl in DFs.
      assert (| Γ', Fs, ˝v | ↓).
      { eapply value_terminates_env_indep; eauto. }
      destruct H as [k' Hterm'].
      destruct (termination_semantics _ _ _ _ Hterm') as [Γ'' [w Hw]].
      eapply semantics_terminates.
      exists (k + k'), Γ''.
      eapply transitive_eval; eauto.
Qed.
