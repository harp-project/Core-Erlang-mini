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

Lemma biforall_vrel_closed : forall vals1 vals2 m,
  list_biforall (Vrel m) vals1 vals2 ->
  Forall (fun e => VALCLOSED e) vals1 /\ Forall (fun e => VALCLOSED e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; repeat constructor.
  * eapply Vrel_closed_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Vrel_closed_r; eauto.
  * eapply IHvals1; eauto.
Qed.

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
      do 2 rewrite subst_comp. apply H0.
      split. 2: split.
      1-2: rewrite subst_list_extend; auto.
      1: rewrite <- H5. 2: apply Nat.eqb_eq in Heqb; rewrite <- Heqb in H6; rewrite <- H6.
      1-2: apply scoped_list_subscoped; auto; apply biforall_vrel_closed in H7; apply H7.
      rewrite subst_list_extend, subst_list_extend; auto. intros.
      pose (list_subst_get_possibilities x vals1 ξ₁).
      pose (list_subst_get_possibilities x vals2 ξ₂).
      assert (length vals1 = length vals2). { lia. } rewrite H9 in *.
      destruct o, o0, H10, H11; try lia.
      ** rewrite H10, H11. apply indexed_to_biforall. exact H7. lia.
      ** rewrite H10, H11. specialize (H4 (x - length vals2)).
         repeat break_match_goal; auto. eapply Vrel_downclosed.
         all: apply H4; lia.
    + apply Nat.eqb_neq in Heqb. contradiction.
Unshelve. lia.
Qed.

Fixpoint make_vars (n : nat) (l : list Var) : list Exp :=
match l with
| [] => []
| x::xs => EVar n x :: (make_vars (S n) xs)
end.

Fixpoint unwinding (n : nat) (f : FunctionIdentifier) (vl : list Var) (b : Exp) : Exp :=
match n with
| 0 => ERecFun f vl (EApp (EFunId 0 f) (make_vars 1 vl))
| S n' => EFun vl b.[unwinding n' f vl b/]
end.

Theorem unwinding_term :
  forall f vl b fs e m, | fs, e.[ERecFun f vl b/] | m ↓ <-> exists n, | fs, e.[unwinding n f vl b/] | m ↓.
Proof.
  (* TODO *)
Abort.

Lemma Vrel_RecFun_compat :
  forall Γ f1 f2 vl1 vl2 b1 b2, length vl1 = length vl2 ->
  Erel_open (S (length vl1) + Γ) b1 b2 ->
  Vrel_open Γ (ERecFun f1 vl1 b1) (ERecFun f2 vl2 b2).
Proof.
  intros. unfold Vrel_open. intros.
  inversion H1 as [? [? ?] ].
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor. Search Erel ExpScoped. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. eapply subst_preserves_scope_exp in H0. exact H0.
    Search subscoped. replace (S (length vl1)) with (S (length vl1) + 0) at 2 by lia.
    fold_upn. eapply upn_scope. auto.
  - constructor. Search Erel ExpScoped. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. rewrite H in H5. eapply subst_preserves_scope_exp in H5. exact H5.
    Search subscoped. replace (S (length vl2)) with (S (length vl2) + 0) at 2 by lia.
    fold_upn. eapply upn_scope. auto.
  - break_match_goal.
    2: { apply Nat.eqb_neq in Heqb. congruence. }
    + intros. unfold Erel_open, Erel in H0.
      do 2 rewrite subst_comp. apply H0.
      split. 2: split.
      1-2: fold_upn; rewrite subst_list_extend; auto.
      1: rewrite <- H5. 2: apply Nat.eqb_eq in Heqb; rewrite <- Heqb in H6; rewrite <- H6.
      * replace (S (Datatypes.length vals1)) with (length (ERecFun f1 vl1 b1.[upn (S (Datatypes.length vals1)) ξ₁] :: vals1)) by auto.
        apply scoped_list_subscoped; auto. apply biforall_vrel_closed in H7.
        constructor. 2: apply H7; auto. admit.
      * simpl. lia.
      * apply Nat.eqb_eq in Heqb. repeat rewrite <- H6, <- H5.
        replace (S (Datatypes.length vals1)) with (length (ERecFun f2 vl2 b2.[upn (S (Datatypes.length vals2)) ξ₂] :: vals2)). 2: simpl; lia.
        apply scoped_list_subscoped; auto. apply biforall_vrel_closed in H7.
        constructor. 2: apply H7; auto. admit.
      * simpl. lia.

      *
      do 2 fold_upn. rewrite subst_list_extend, subst_list_extend; auto. intros.
      destruct x; simpl.
      ** constructor.
      admit.
Admitted.

Ltac unfold_hyps :=
match goal with
| [ H: exists _, _ |- _] => destruct H
| [ H: _ /\ _ |- _] => destruct H
end.

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
  do 2 unfold_hyps. subst. destruct H0, H1. eapply H3; eauto.
  do 5 unfold_hyps. subst.
  destruct H1, H1. subst. eapply H3; eauto. eapply Vrel_downclosed. eauto.
  do 7 unfold_hyps. subst.
  destruct H1, H1. subst. eapply H3; eauto. eapply Vrel_downclosed. eauto.
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

Ltac inversion_is_value :=
match goal with
| [ H: is_value _ |- _ ] => inversion H; clear H
end.

Lemma Vrel_is_value : forall v1 v2 m, Vrel m v1 v2 -> is_value v1 /\ is_value v2.
Proof.
  intros. rewrite Vrel_Fix_eq in H. destruct H, H0, v1, v2; try inversion H; try inversion H0. all: repeat constructor; contradiction.
Qed.

Lemma Erel_Plus_compatible_closed : forall n e1 e2 e1' e2',
    Erel n e1 e1' -> Erel n e2 e2' ->
    Erel n (EPlus e1 e2) (EPlus e1' e2').
Proof.
  intros. destruct H, H0, H1, H2.
  split. 2: split. 1-2: constructor; auto.
  intros. destruct H5, H7.
  destruct m. inversion H6. inversion H9.
  inversion H6; try inversion_is_value. subst.
  epose (H3 m _ (FPlus1 e2 ::F1) (FPlus1 e2' ::F2) _ H11).
  destruct t. exists (S x). constructor. auto.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; auto. intros. apply Vrel_is_value in H9 as v. destruct v.
  inversion H10; subst. 2-6: inversion H12.
  epose (H4 k _ (FPlus2 v1 H14 :: F1) (FPlus2 v2 H13 :: F2) _ H19). destruct t.
  exists (S x). econstructor; eauto.

  Unshelve. lia.
  split. 2: split. 1-2: constructor; apply Vrel_closed in H9; destruct H9; auto.
  intros. apply Vrel_is_value in H15 as v. destruct v. inversion H16; subst.
  2-6 : inversion H17.
  eapply H8 in H25. destruct H25. exists (S x).
  (** LHS, RHS is literal: *)
  rewrite Vrel_Fix_eq in H15. destruct H15, H21. destruct v3; inversion H22. subst.
  rewrite Vrel_Fix_eq in H9. destruct H9, H22. destruct v2; inversion H24. subst.
  apply term_plus_right. subst. exact H20. lia. apply Vrel_Lit_compat_closed.
Qed.


Lemma Erel_If_compatible_closed : forall n e1 e2 e1' e2' e3 e3',
    Erel n e1 e1' -> Erel n e2 e2' -> Erel n e3 e3' ->
    Erel n (EIf e1 e2 e3) (EIf e1' e2' e3').
Proof.
  intros.
  destruct H, H0, H1, H2, H3, H4.
  split. 2: split. 1-2: constructor; auto.
  intros. destruct H8, H10.
  destruct m. inversion H9. inversion H12.
  inversion H9; try inversion_is_value. subst.
  epose (H5 m _ (FIf e2 e3 ::F1) (FIf e2' e3' ::F2) _ H14).
  destruct t. exists (S x). constructor. auto.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; auto. intros. apply Vrel_is_value in H12 as v. destruct v.
  inversion H13; subst. 3-7: inversion H15.
  * rewrite Vrel_Fix_eq in H12. destruct H12, H17. destruct v2; inversion H18. subst.
    epose (H6 k _ F1 F2 _ H22). destruct t.
    exists (S x). econstructor; eauto.
  * epose (H7 k _ F1 F2 _ H24). destruct t.
    exists (S x). econstructor; eauto.
    rewrite Vrel_Fix_eq in H12. destruct H12, H18. destruct v1, v2; subst; auto.
    congruence. congruence.

  Unshelve.
  1, 3: lia.
  split. 2: split. all: auto. intros. eapply (H11 m0 _ _ _ H18 H20).
  split. 2: split. all: auto. intros. eapply (H11 m0 _ _ _ H17 H18).
  Unshelve. all: lia.
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
