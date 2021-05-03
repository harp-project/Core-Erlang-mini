Require Import LogRel.
Import ListNotations.

Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall v1 v2, CIU_equivalent_values v1 v2 ->
  (exists clock, eval clock e1 = Res v1) <-> (exists clock, eval clock e2 = Res v2).

Definition CIU_open (Γ : list VarFunId) (e1 e2 : Exp) :=
  forall ξ, subscoped Γ [] ξ ->
  CIU (subst ξ e1) (subst ξ e2).

Lemma CIU_closed :
  forall e1 e2,
  CIU e1 e2 -> EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.


Lemma Erel_implies_CIU : forall Γ e1 e2,
  Erel_open Γ e1 e2 ->
  CIU_open Γ e1 e2.
Proof.
  intros. unfold CIU_open, CIU; intros.
  split. 2: split. 3: assert (EXPCLOSED (subst ξ e1) /\ EXPCLOSED (subst ξ e2)).
  1-3: eapply Erel_open_closed in H; eauto; apply H.
  intros. destruct H1. unfold Erel_open, Erel in H. unfold exp_rel in H.
  split; intros; inversion H3.
  - unfold CIU_equivalent_values in H2. destruct H2, H2.
Qed.
