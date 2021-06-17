Require Export Compatibility.

Import ListNotations.

Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall F, FCLOSED F -> | F, e1 | ↓ -> | F, e2 | ↓.

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
