Require Import LogRel.
Import ListNotations.

Lemma Vrel_Var_compat :
  forall Γ n x,
  n < Γ ->
  Vrel_open Γ (EVar n x) (EVar n x).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; auto; contradiction.
Qed.

Hint Resolve Vrel_Var_compat.

Lemma Vrel_FunId_compat :
  forall Γ n x,
  n < Γ ->
  Vrel_open Γ (EFunId n x) (EFunId n x).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; auto; contradiction.
Qed.

Hint Resolve Vrel_FunId_compat.

Lemma Vrel_Lit_compat_closed :
  forall m n,
  Vrel m (ELit n) (ELit n).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
Qed.

Hint Resolve Vrel_Lit_compat_closed.

Lemma Vrel_Lit_compat_open :
  forall Γ n,
  Vrel_open Γ (ELit n) (ELit n).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Hint Resolve Vrel_Lit_compat_open.

Lemma Vrel_Fun_compat :
  forall Γ vl1 vl2 b1 b2, length vl1 = length vl2 ->
  Erel_open (length vl1 + Γ) b1 b2 ->
  Vrel_open Γ (EFun vl1 b1) (EFun vl2 b2).
Proof.
  intros. unfold Vrel_open. intros.
  inversion H1 as [? [? ?] ].
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor. Search Erel ExpScoped. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. eapply subst_preserves_scope_exp in H0. exact H0.
    Search subscoped. replace (length vl1) with (length vl1 + 0) at 2 by lia. eapply upn_scope. auto.
  - constructor. Search Erel ExpScoped. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. rewrite H in H5. eapply subst_preserves_scope_exp in H5. exact H5.
    Search subscoped. replace (length vl2) with (length vl2 + 0) at 2 by lia. eapply upn_scope. auto.
  - break_match_goal.
    + intros. unfold Erel_open, Erel in H0.
      rewrite substcomp_subst, substcomp_subst. apply H0.
      split. 2: split.
      * Search upn subscoped.
    + apply Nat.eqb_neq in Heqb. contradiction.
Admitted.

Lemma Vrel_RecFun_compat :
  forall Γ f vl b1 b2,
  Erel_open (Γ ++ inr f::map inl vl) b1 b2 ->
  Vrel_open Γ (ERecFun f vl b1) (ERecFun f vl b2).
Proof.

Admitted.

Lemma Erel_Val_compatible_closed :
  forall {n v v'},
    Vrel n v v' ->
    Erel n v v'.
Proof.
  intros.
  unfold Erel, exp_rel.
  pose proof (Vrel_possibilities H).
  intuition eauto.
  1-2, 4, 5, 7, 8: apply Vrel_closed in H; destruct H.
  1-7: repeat try constructor; auto.
  destruct H1, H1; subst. destruct m; inversion H0. subst.
  eexists. split. exists 1. reflexivity. eapply Vrel_downclosed. eauto.
  destruct H0, H0, H0, H0, H0. subst. destruct m; inversion H1. subst.
  eexists. split. exists 1. reflexivity. eapply Vrel_downclosed. eauto.
  destruct H0, H0, H0, H0, H0, H0, H0. subst. destruct m; inversion H1. subst.
  eexists. split. exists 1. reflexivity. eapply Vrel_downclosed. eauto.
Unshelve. all: auto.
Qed.

Hint Resolve Erel_Val_compatible_closed.

Lemma Erel_Val_compatible :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ v v'.
Proof.
  intros.
  unfold Erel_open, Vrel_open in *.
  auto.
Qed.

Hint Resolve Erel_Val_compatible.

Ltac unfold_hyps :=
match goal with
| [ H: exists _, _ |- _] => destruct H
| [ H: _ /\ _ |- _] => destruct H
end.

Lemma Erel_Plus_compatible_closed : forall n e1 e2 e1' e2',
    Erel n e1 e1' -> Erel n e2 e2' ->
    Erel n (EPlus e1 e2) (EPlus e1' e2').
Proof.
  intros.
  destruct (Erel_closed H). destruct (Erel_closed H0).
  unfold Erel, exp_rel.
  split. 2: split. 1-2: constructor; auto.
  intros. destruct m. inversion H5.
  simpl in H5. break_match_hyp; try congruence. destruct v; break_match_hyp. all: try congruence.
  destruct v; try congruence. inversion H5. subst.
  apply H in Heqr. apply H0 in Heqr0. 2-3: lia. destruct Heqr, Heqr0, H6, H7, H6, H7.
  apply Vrel_possibilities in H8. apply Vrel_possibilities in H9. intuition; repeat unfold_hyps; try congruence.
  subst. exists (ELit (l + l0)). split. exists (S (x1 + x2)). simpl.
  eapply bigger_clock in H6. eapply bigger_clock in H7. rewrite H6, H7. inversion H8. inversion H9. auto. 1-2: lia.
  repeat constructor.
Qed.


Lemma Erel_If_compatible_closed : forall n e1 e2 e1' e2' e3 e3',
    Erel n e1 e1' -> Erel n e2 e2' -> Erel n e3 e3' ->
    Erel n (EIf e1 e2 e3) (EIf e1' e2' e3').
Proof.
  intros.
  destruct (Erel_closed H). destruct (Erel_closed H0). destruct (Erel_closed H1).
  unfold Erel, exp_rel.
  split. 2: split. 1-2: constructor; auto.
  intros. destruct m. inversion H8.
  simpl in H8. break_match_hyp; try congruence. destruct v. destruct l.
  * apply H in Heqr. apply H0 in H8. 2-3: lia. destruct Heqr, H8, H9, H8, H9, H8.
    apply Vrel_possibilities in H10. intuition; repeat unfold_hyps; try congruence. subst.
    inversion H10. subst. exists x0. split. exists (S (x1 + x2)). simpl.
    eapply bigger_clock in H8. eapply bigger_clock in H9. rewrite H8, H9. auto. 1-2: lia.
    admit.
  * (* these are all provable *)
Qed.

(*
Lemma Expr_cons :
  forall n (e1 e2 : Expr),
    (forall m (Hmn : m <= n) v1 v2,
        Vrel m v1 v2 -> Erel m e1.[v1/] e2.[v2/]) ->
    forall m (Hmn : m <= n) e1' e2',
      Erel m e1' e2' ->
      Erel m (Seq e1' e1) (Seq e2' e2).
Proof.
  intros.
  destruct (Erel_closed H0) as [IsClosed_e1 IsClosed_e2].
  unfold Erel, Erel'.
  split; [|split];
    try solve [specialize (H 0 ltac:(auto) _ _ (Vrel_Const_compatible_closed 0 0));
               constructor; eauto using sub_implies_scope_exp_1].
  intros.
  run_μeval_for 1.
  run_μeval_star_for 1.
  eapply H0; eauto 6.
Qed.

Hint Resolve Expr_cons.

Lemma Erel_Var_compatible :
  forall Γ x,
    x < Γ ->
    Erel_open Γ (Var x) (Var x).
Proof.
  auto.
Qed.

Hint Resolve Erel_Var_compatible.

Lemma Erel_Const_compatibile :
  forall Γ r,
    Erel_open Γ (Const r) (Const r).
Proof.
  auto.
Qed.

Hint Resolve Erel_Var_compatible.

(* Lemma 5: compatible under Fun *)
Lemma Erel_Fun_compatible :
  forall Γ e e',
    Erel_open (S Γ) e e' ->
    Erel_open Γ (Fun e) (Fun e').
Proof.
  auto.
Qed.

Hint Resolve Erel_Fun_compatible.

Lemma Erel_Seq_compatible :
  forall Γ (e1 e2 e1' e2': Expr),
    Erel_open (S Γ) e1 e2 ->
    Erel_open Γ e1' e2' ->
    Erel_open Γ (Seq e1' e1) (Seq e2' e2).
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Expr_cons; auto.
  intros.
  asimpl.
  eauto.
Qed.

Hint Resolve Erel_Seq_compatible.

Lemma Vrel_open_Erel_open :
  forall Γ v v',
    Vrel_open Γ v v' -> Erel_open Γ v v'.
Proof.
  eauto.
Qed.

Hint Resolve Vrel_open_Erel_open.
*)

Theorem Vrel_Fundamental_closed :
  forall (v : Exp),
    VALCLOSED v ->
    forall n, Vrel n v v.
Proof.
Admitted.

Theorem exp_rel_trans :
  forall n vrel e1 e2 e3,
    exp_rel n vrel e1 e2 -> exp_rel n vrel e2 e3 -> exp_rel n vrel e1 e3.
Proof.
  intros. unfold exp_rel in *. destruct H, H0, H1, H2. intuition.
  specialize (H3 _ Hmn _ H5). destruct H3, H3, H3.
Abort.

Theorem Vrel_closed_trans :
  forall n (v1 v2 v3 : Exp),
    Vrel n v1 v2 -> Vrel n v2 v3 -> Vrel n v1 v3.
Proof.
  induction n.
  {
  intros.
  rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq in H0. rewrite Vrel_Fix_eq.
  destruct v1.
  2-3, 6-10: inversion H; inversion H2; contradiction.
  all: destruct v2.
  all: try inversion H; try inversion H2; try contradiction.
  all: destruct v3.
  all: try inversion H0; try inversion H6; try contradiction.
  all: subst.
  * unfold Vrel_rec. split. 2: split. all: constructor.
  * clear H2 H6. break_match_hyp. break_match_hyp. 2-3: contradiction.
    subst. unfold Vrel_rec. intuition. break_match_goal. 2: contradiction. intros. inversion Hmn.
  * clear H2 H6. break_match_hyp. break_match_hyp. 2-3: contradiction.
    subst. unfold Vrel_rec. intuition. break_match_goal. 2: contradiction. intros. inversion Hmn.
  }
  {
  intros.
  rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq in H0. rewrite Vrel_Fix_eq.
  destruct v1.
  2-3, 6-10: inversion H; inversion H2; contradiction.
  all: destruct v2.
  all: try inversion H; try inversion H2; try contradiction.
  all: destruct v3.
  all: try inversion H0; try inversion H6; try contradiction.
  all: subst.
  * unfold Vrel_rec. split. 2: split. all: constructor.
  * clear H2 H6. break_match_hyp. break_match_hyp. 2-3: contradiction.
    subst. unfold Vrel_rec. intuition. break_match_goal. 2: contradiction. intros.
    specialize (H8 m Hmn vals1 vals2 H2 H6 H9).
    specialize (H4 m Hmn vals1 vals2 H2 H6 H9). admit.
  * admit.
  }
Admitted.
