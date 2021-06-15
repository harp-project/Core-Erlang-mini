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

Hint Resolve Vrel_Fun_compat.

(* Fixpoint make_vars (n : nat) (l : list Var) : list Exp :=
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
Abort. *)

Import Coq.Arith.Wf_nat.

Lemma Vrel_RecFun_compat :
  forall Γ f1 f2 vl1 vl2 b1 b2, length vl1 = length vl2 ->
  Erel_open (S (length vl1) + Γ) b1 b2 ->
  Vrel_open Γ (ERecFun f1 vl1 b1) (ERecFun f2 vl2 b2).
Proof.
  intros. unfold Vrel_open. induction n using lt_wf_ind. intros.
  assert (forall m : nat,
     m < n ->
     forall ξ₁ ξ₂ : Substitution,
     Grel m Γ ξ₁ ξ₂ -> Vrel m (ERecFun f1 vl1 b1).[ξ₁] (ERecFun f2 vl2 b2).[ξ₂]) as IH. auto. clear H1.
    
  inversion H2 as [? [? ?] ].
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
        constructor. 2: apply H7; auto. simpl.
        epose (IH m Hmn ξ₁ ξ₂ _). apply Vrel_closed_l in v. simpl in v.
        rewrite H5. exact v.
      * simpl. lia.
      * apply Nat.eqb_eq in Heqb. repeat rewrite <- H6, <- H5.
        replace (S (Datatypes.length vals1)) with (length (ERecFun f2 vl2 b2.[upn (S (Datatypes.length vals2)) ξ₂] :: vals2)). 2: simpl; lia.
        apply scoped_list_subscoped; auto. apply biforall_vrel_closed in H7.
        constructor. 2: apply H7; auto. simpl.
        epose (IH m Hmn ξ₁ ξ₂ _). apply Vrel_closed_r in v. simpl in v.
        rewrite H6. exact v.
      * simpl. lia.

      *
      do 2 fold_upn. rewrite subst_list_extend, subst_list_extend; auto. intros.
      destruct x; simpl.
      ** apply IH; auto. eapply Grel_downclosed. eauto.
      ** pose (list_subst_get_possibilities x vals1 ξ₁).
         pose (list_subst_get_possibilities x vals2 ξ₂).
         assert (length vals1 = length vals2). { lia. } rewrite H9 in *.
         destruct o, o0, H10, H11; try lia.
         -- rewrite H10, H11. apply indexed_to_biforall. exact H7. lia.
         -- rewrite H10, H11. specialize (H4 (x - length vals2)).
         repeat break_match_goal; auto. eapply Vrel_downclosed.
         all: apply H4; lia.
      ** simpl. auto.
      ** simpl. auto.
  Unshelve.
  1-2: eapply Grel_downclosed; eauto.
  1-2: lia.
  Unshelve.
  1-2: lia.
Qed.

Hint Resolve Vrel_RecFun_compat.

Ltac unfold_hyps :=
match goal with
| [ H: exists _, _ |- _] => destruct H
| [ H: _ /\ _ |- _] => destruct H
end.

Lemma Erel_Val_compat_closed :
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

Hint Resolve Erel_Val_compat_closed.

Lemma Erel_Val_compat :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ v v'.
Proof.
  intros.
  unfold Erel_open, Vrel_open in *.
  auto.
Qed.

Hint Resolve Erel_Val_compat.

Lemma Vrel_open_Erel_open :
  forall Γ v v',
    Vrel_open Γ v v' -> Erel_open Γ v v'.
Proof.
  eauto.
Qed.

Hint Resolve Vrel_open_Erel_open.

Ltac inversion_is_value :=
match goal with
| [ H: is_value _ |- _ ] => inversion H; clear H
end.

Lemma Vrel_is_value : forall v1 v2 m, Vrel m v1 v2 -> is_value v1 /\ is_value v2.
Proof.
  intros. rewrite Vrel_Fix_eq in H. destruct H, H0, v1, v2; try inversion H; try inversion H0. all: repeat constructor; contradiction.
Qed.

Lemma Erel_Plus_compat_closed : forall n e1 e2 e1' e2',
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


Lemma Erel_If_compat_closed : forall n e1 e2 e1' e2' e3 e3',
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

Lemma Erel_Var_compat :
  forall Γ n x,
    n < Γ ->
    Erel_open Γ (EVar n x) (EVar n x).
Proof.
  auto.
Qed.

Hint Resolve Erel_Var_compat.

Lemma Erel_FunId_compat :
  forall Γ n x,
    n < Γ ->
    Erel_open Γ (EVar n x) (EVar n x).
Proof.
  auto.
Qed.

Hint Resolve Erel_FunId_compat.

Lemma Erel_Lit_compat :
  forall Γ l,
    Erel_open Γ (ELit l) (ELit l).
Proof.
  auto.
Qed.

Hint Resolve Erel_Lit_compat.

Lemma Erel_Fun_compat :
  forall Γ vl vl' b b', length vl = length vl' ->
    Erel_open (length vl + Γ) b b' ->
    Erel_open Γ (EFun vl b) (EFun vl' b').
Proof.
  auto.
Qed.

Hint Resolve Erel_Fun_compat.

Lemma Erel_RecFun_compat :
  forall Γ f f' (vl vl' : list Var) b b', length vl = length vl' ->
    Erel_open (S (length vl) + Γ) b b' ->
    Erel_open Γ (ERecFun f vl b) (ERecFun f' vl' b').
Proof.
  auto.
Qed.

Hint Resolve Erel_RecFun_compat.

Lemma Erel_Let_compat_closed :
  forall n x y (e2 e2' : Exp),
    (forall m (Hmn : m <= n) v2 v2',
        Vrel m v2 v2' -> Erel m e2.[v2/] e2'.[v2'/]) ->
    forall m (Hmn : m <= n) e1 e1',
      Erel m e1 e1' ->
      Erel m (ELet x e1 e2) (ELet y e1' e2').
Proof.
  intros.
  destruct (Erel_closed H0) as [IsClosed_e1 IsClosed_e2].
  unfold Erel, exp_rel. specialize (H 0 ltac:(lia) (ELit 0) (ELit 0) (Vrel_Lit_compat_closed 0 0)) as H'.
  split. 2: split.
  * apply Erel_closed_l in H'. constructor; auto.
    Search subst ExpScoped. apply subst_implies_scope_exp_1; auto.
  * apply Erel_closed_r in H'. constructor; auto.
    Search subst ExpScoped. apply subst_implies_scope_exp_1; auto.
  * intros. destruct m0; inversion H2; try inversion_is_value. subst.
    destruct H0, H3. eapply H4 in H5. destruct H5. exists (S x0). constructor. exact H5.
    lia.

    apply Erel_closed_l in H' as e1H. apply subst_implies_scope_exp_1 in e1H.
    apply Erel_closed_r, subst_implies_scope_exp_1 in H' as e2H.
    destruct H1, H6.
    split. 2: split. 1-2: constructor; auto.
    intros. apply Vrel_is_value in H8 as v. destruct v.
    inversion H9; subst. 2-6: inversion H10. eapply H in H17. destruct H17.
    exists (S x0). constructor. auto. exact H12. 2: exact H8. lia. lia.

    split. 2: split. all: auto. intros. eapply H7. 3: exact H16. lia. auto.
Qed.

Hint Resolve Erel_Let_compat_closed.


Lemma Erel_Let_comaptible :
  forall Γ x x' (e1 e1' e2 e2': Exp),
    Erel_open Γ e1 e1' ->
    Erel_open (S Γ) e2 e2' ->
    Erel_open Γ (ELet x e1 e2) (ELet x' e1' e2').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_Let_compat_closed; auto.
  intros. Search scons subst.
  do 2 rewrite subst_comp, substcomp_scons, substcomp_id_r. apply H0.
  apply Vrel_closed in H2 as v. destruct v.
  split. 2: split.
  1-2: intro; intros; destruct v; cbn; auto; apply H1; lia.
  intros. destruct x0; auto. simpl. destruct H1, H6. specialize (H7 x0 ltac:(lia)).
  break_match_goal. break_match_goal; auto. eapply Vrel_downclosed; eauto. lia.
  Unshelve. lia.
Qed.

Hint Resolve Erel_Let_comaptible.

Lemma Erel_LetRec_compat_closed :
  forall n f1 f2 vl1 vl2 (b b' e e' : Exp) m (Hmn : m <= n)
  (CL1 : EXP S (length vl1) ⊢ b) (CL1 : EXP S (length vl2) ⊢ b')
  (CL1 : EXP 1 ⊢ e) (CL1 : EXP 1 ⊢ e'),
  (* length vl1 = length vl2 -> *)
    (* (forall m (Hmn : m <= n),  *)
      Erel m e.[ERecFun f1 vl1 b/] e'.[ERecFun f2 vl2 b'/] (* ) *) ->
    (* (forall m (Hmn : m <= n) vals1 vals2,
        length vals1 = length vl1 ->
        list_biforall (Vrel m) vals1 vals2 ->
        Erel m e.[list_subst (ERecFun f1 vl1 b :: vals1) idsubst] 
               e'.[list_subst (ERecFun f2 vl2 b' :: vals2) idsubst]) -> *)
      Erel m (ELetRec f1 vl1 b e) (ELetRec f2 vl2 b' e').
Proof.
  (* induction n using lt_wf_ind. intros. *)
  intros.
  (* specialize (H0 m Hmn). *)
  (* specialize (H1 m Hmn). *)
  unfold Erel, exp_rel. split. 2: split.
  * constructor. rewrite Nat.add_0_r. auto. auto.
  * constructor. rewrite Nat.add_0_r. auto. auto.
  * intros. inversion H1; try inversion_is_value. subst.
    destruct H0, H2. eapply H in H8. destruct H8. exists (S x). constructor.
    exact H4. lia. split. 2: split. all: auto.
    intros. eapply H3 in H7. exact H7. lia. auto.
Qed.

Hint Resolve Erel_LetRec_compat_closed.


Lemma Erel_LetRec_compat :
  forall Γ f1 f2 vl1 vl2 (e1 e1' e2 e2': Exp), length vl1 = length vl2 ->
    Erel_open (S (length vl1) + Γ) e1 e1' ->
    Erel_open (S Γ) e2 e2' ->
    Erel_open Γ (ELetRec f1 vl1 e1 e2) (ELetRec f2 vl2 e1' e2').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  apply Erel_open_scope in H0 as e1CL.
  apply Erel_open_scope in H1 as e2CL.
  assert (EXP S (length vl1) ⊢ e1.[upn (S (length vl1)) ξ₁]) as E1SC. {
    destruct e1CL, e2CL.
    pose (subst_preserves_scope_exp).
    pose (i e1 (S (length vl1) + Γ)) as HH. destruct HH. clear H8.
    apply (H7 H3 (S (length vl1)) (upn (S (length vl1)) ξ₁)).
    replace (S (length vl1)) with (S (length vl1) + 0) at 2 by lia.
    apply upn_scope. apply H2.
  }
  assert (EXP S (length vl2) ⊢ e1'.[upn (S (length vl2)) ξ₂]) as E1'SC. {
    destruct e1CL, e2CL.
    pose (subst_preserves_scope_exp).
    pose (i e1' (S (length vl2) + Γ)) as HH. destruct HH. clear H8. rewrite H in H4.
    apply (H7 H4 (S (length vl2)) (upn (S (length vl2)) ξ₂)).
    replace (S (length vl2)) with (S (length vl2) + 0) at 2 by lia.
    apply upn_scope. apply H2.
  }
  assert (EXP 1 ⊢ e2.[up_subst ξ₁]) as E2SC. {
    destruct e1CL, e2CL.
    pose (subst_preserves_scope_exp).
    pose (i e2 (S Γ)) as HH. destruct HH. clear H8.
    apply (H7 H5 1 (up_subst ξ₁)). replace 1 with (1 + 0) by lia.
    apply up_scope. apply H2.
  }
  assert (EXP 1 ⊢ e2'.[up_subst ξ₂]) as E2'SC. {
    destruct e1CL, e2CL.
    pose (subst_preserves_scope_exp).
    pose (i e2' (S Γ)) as HH. destruct HH. clear H8.
    apply (H7 H6 1 (up_subst ξ₂)). replace 1 with (1 + 0) by lia.
    apply up_scope. apply H2.
  }
  eapply Erel_LetRec_compat_closed; auto.
  * intros. do 2 rewrite subst_comp, substcomp_scons, substcomp_id_r. apply H1.
    inversion H2. destruct H4. split. 2: split.
    - intro. intros. destruct v; simpl.
      + eapply Vrel_RecFun_compat, Erel_Val_compat, Erel_open_closed in H0.
        2: exact H3. 2: auto.
        destruct H0. inversion H0. simpl in H8. exact H8.
      + apply H2. lia.
    - intro. intros. destruct v; simpl.
      + rewrite H in H0.
        eapply Vrel_RecFun_compat, Erel_Val_compat, Erel_open_closed in H0.
        2: exact H4. 2: auto.
        destruct H0. inversion H7. simpl in H8. exact H8.
      + apply H4. lia.
    - intros. destruct x.
      + simpl. eapply Vrel_RecFun_compat; eauto. (* eapply Grel_downclosed; eauto. *)
      + simpl. specialize (H5 x ltac:(lia)).
        break_match_goal. break_match_goal. all: try lia. eapply Vrel_downclosed; eauto.
(*   * admit. *)
Unshelve.
1-2: exact ("f"%string, 0).
all: lia.
Qed.

Hint Resolve Erel_LetRec_compat.

