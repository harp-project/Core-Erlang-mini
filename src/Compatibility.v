Require Export LogRel.
Import ListNotations.

Lemma Vrel_Var_compat :
  forall Γ n,
  n < Γ ->
  Vrel_open Γ (EVar n) (EVar n).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; auto; contradiction.
Qed.

Global Hint Resolve Vrel_Var_compat : core.

Lemma Vrel_FunId_compat :
  forall Γ n,
  n < Γ ->
  Vrel_open Γ (EFunId n) (EFunId n).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; auto; contradiction.
Qed.

Global Hint Resolve Vrel_FunId_compat : core.

Lemma Vrel_Lit_compat_closed :
  forall m l,
  Vrel m (ELit l) (ELit l).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
Qed.

Global Hint Resolve Vrel_Lit_compat_closed : core.

Lemma Vrel_Lit_compat :
  forall Γ l,
  Vrel_open Γ (ELit l) (ELit l).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Lit_compat : core.

Lemma Vrel_Pid_compat_closed :
  forall m p,
  Vrel m (EPid p) (EPid p).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
Qed.

Global Hint Resolve Vrel_Pid_compat_closed : core.

Lemma Vrel_Pid_compat :
  forall Γ p,
  Vrel_open Γ (EPid p) (EPid p).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Pid_compat : core.

Lemma Vrel_Nil_compat_closed:
  forall m, Vrel m ENil ENil.
Proof.
  split; constructor; constructor.
Qed.

Global Hint Resolve Vrel_Nil_compat_closed : core.

Lemma Vrel_Nil_compat :
  forall Γ, Vrel_open Γ ENil ENil.
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Nil_compat : core.

Lemma Vrel_Cons_compat_closed :
  forall m v1 v1' v2 v2', Vrel m v1 v1' -> Vrel m v2 v2'
 ->
  Vrel m (VCons v1 v2) (VCons v1' v2').
Proof.
  intros. rewrite Vrel_Fix_eq. split. 2: split. 1-2: constructor.
  * apply Vrel_closed in H. apply H.
  * apply Vrel_closed in H0. apply H0.
  * apply Vrel_closed in H. apply H.
  * apply Vrel_closed in H0. apply H0.
  * intros. rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq in H0.
    split; [apply H | apply H0].
  Unshelve. all: lia.
Qed.

Global Hint Resolve Vrel_Cons_compat_closed : core.

Lemma Vrel_Cons_compat :
  forall Γ v1 v1' v2 v2', Vrel_open Γ v1 v1' -> Vrel_open Γ v2 v2'
 ->
  Vrel_open Γ (VCons v1 v2) (VCons v1' v2').
Proof.
  intros. unfold Vrel_open. intros. simpl.
  apply Vrel_Cons_compat_closed; [apply H | apply H0]; auto.
Qed.

Global Hint Resolve Vrel_Cons_compat : core.

Lemma Vrel_Fun_compat :
  forall Γ vl1 vl2 b1 b2, length vl1 = length vl2 ->
  Erel_open (S (length vl1) + Γ) b1 b2 ->
  Vrel_open Γ (EFun vl1 b1) (EFun vl2 b2).
Proof.
  intros. unfold Vrel_open. induction n using lt_wf_ind. intros.
  assert (forall m : nat,
     m < n ->
     forall ξ₁ ξ₂ : Substitution,
     Grel m Γ ξ₁ ξ₂ -> Vrel m (EFun vl1 b1).[ξ₁] (EFun vl2 b2).[ξ₂]) as IH. auto. clear H1.
    
  inversion H2 as [? [? ?] ].
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. eapply subst_preserves_scope_exp in H0. exact H0.
    replace (S (length vl1)) with (S (length vl1) + 0) at 2 by lia.
    fold_upn. eapply upn_scope. auto.
  - constructor. rewrite Nat.add_0_r. eapply Erel_open_scope in H0.
    destruct H0. rewrite H in H5. eapply subst_preserves_scope_exp in H5. exact H5.
    replace (S (length vl2)) with (S (length vl2) + 0) at 2 by lia.
    fold_upn. eapply upn_scope. auto.
  - break_match_goal.
    2: { apply Nat.eqb_neq in Heqb. congruence. }
    + intros. unfold Erel_open, Erel in H0.
      do 2 rewrite subst_comp. epose proof (nH0 := H0 m _ _ _).
      destruct nH0 as [nCl1 [nCl2 nH0]].
      split. 2: split. exact nCl1. exact nCl2. intros. eapply nH0. 3: exact H9.
      lia. auto.
    Unshelve.
      split. 2: split.
      1-2: fold_upn; rewrite subst_list_extend; auto.
      1: rewrite <- H5. 2: apply Nat.eqb_eq in Heqb; rewrite <- Heqb in H6; rewrite <- H6.
      * replace (S (Datatypes.length vals1)) with (length (EFun vl1 b1.[upn (S (Datatypes.length vals1)) ξ₁] :: vals1)) by auto.
        apply scoped_list_subscoped; auto. apply biforall_vrel_closed in H7.
        constructor. 2: apply H7; auto. simpl.
        epose (IH m Hmn ξ₁ ξ₂ _). apply Vrel_closed_l in v. simpl in v.
        rewrite H5. exact v.
      * simpl. lia.
      * apply Nat.eqb_eq in Heqb. repeat rewrite <- H6, <- H5.
        replace (S (Datatypes.length vals1)) with (length (EFun vl2 b2.[upn (S (Datatypes.length vals2)) ξ₂] :: vals2)). 2: simpl; lia.
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

Global Hint Resolve Vrel_Fun_compat : core.

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
  1-2, 4, 5, 7-8, 10-11: apply Vrel_closed in H; destruct H.
  1-8: repeat try constructor; auto.
  * do 2 unfold_hyps. subst. destruct H0, H1. eapply H3; eauto.
  * do 2 unfold_hyps. subst. destruct H1, H1. eapply H3; eauto.
  * do 5 unfold_hyps. subst.
    destruct H0, H1. subst. eapply H3; eauto. eapply Vrel_downclosed. eauto.
  * destruct H1, H3. eapply H4; eauto. eapply Vrel_downclosed. eauto.
  * subst. do 2 constructor.
  * subst. do 2 constructor.
  * subst. destruct H0, H1. eapply H2. 3: exact H3. lia. apply Vrel_Nil_compat_closed.
Unshelve. all: auto.
Qed.

Global Hint Resolve Erel_Val_compat_closed : core.

Lemma Erel_Val_compat :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ v v'.
Proof.
  intros.
  unfold Erel_open, Vrel_open in *.
  auto.
Qed.

Global Hint Resolve Erel_Val_compat : core.

Lemma Vrel_open_Erel_open :
  forall Γ v v',
    Vrel_open Γ v v' -> Erel_open Γ v v'.
Proof.
  eauto.
Qed.

Global Hint Resolve Vrel_open_Erel_open : core.

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
  1-2: constructor; auto; constructor; auto.
  intros. assert (VALCLOSED v1) by (eapply Vrel_closed in H9; apply H9).
  inversion H10; subst. 2-6: inversion H12.
  epose (H4 k _ (FPlus2 v1 (* H14 *) :: F1) (FPlus2 v2 (* H13 *) :: F2) _ H18). destruct t.
  exists (S x). econstructor; eauto.
  inversion_is_value. inversion_is_value.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; apply Vrel_closed in H9; destruct H9; auto; constructor; auto.
  intros. assert (VALCLOSED v0) by (eapply Vrel_closed in H13; apply H13).
  inversion H14; subst.
  2-6 : inversion H16.
  eapply H8 in H22. destruct H22. exists (S x).
  (** LHS, RHS is literal: *)
  rewrite Vrel_Fix_eq in H13. destruct H13, H19. destruct v3; inversion H20. subst.
  rewrite Vrel_Fix_eq in H9. destruct H9, H20. destruct v2; inversion H22. subst.
  apply term_plus_right. subst. exact H17. lia. apply Vrel_Lit_compat_closed.
  inversion_is_value. inversion_is_value.
Qed.

Lemma match_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  (forall l1, 
        (match_pattern p v1 = Some l1 ->
         exists l2, match_pattern p v2 = Some l2 /\ list_biforall (Vrel n) l1 l2)).
Proof.
  intros.
  assert (VALCLOSED v1) by (eapply Vrel_closed in H; apply H).
  assert (VALCLOSED v2) by (eapply Vrel_closed in H; apply H).
  generalize dependent v2. revert n. generalize dependent v1. revert l1. generalize dependent p.
  induction p; destruct v1, v2; intros; try inversion_is_value; rewrite Vrel_Fix_eq in H; destruct H as [Cl1 [Cl2 H]]; try contradiction; simpl in H0; try congruence.
  * break_match_hyp. 2: congruence. inversion H0. subst. exists [].
    split. apply lit_eqb_eq in Heqb. subst. simpl. rewrite lit_eqb_refl. auto.
    constructor.
  * break_match_hyp. 2: congruence. inversion H0. subst. exists [].
    split. apply Nat.eqb_eq in Heqb. subst. simpl. rewrite Nat.eqb_refl. auto.
    constructor.
  * inversion H0. subst. exists [ELit l0]. simpl. split; constructor.
    rewrite Vrel_Fix_eq. simpl; auto. constructor.
  * subst. inversion H0. subst. exists [EPid p0]. split; constructor.
     apply Vrel_Pid_compat_closed. constructor.
  * inversion H0. subst. exists [EFun vl0 v2]; simpl; split; auto.
    constructor. 2: constructor. rewrite Vrel_Fix_eq; simpl; auto.
  * inversion H0; subst. exists [ENil]; split; auto.
    constructor. 2: constructor. apply Vrel_Nil_compat_closed.
  * inversion H0. subst. exists [VCons v2_1 v2_2]; split; auto.
    constructor. 2: constructor. rewrite Vrel_Fix_eq; simpl; auto.
  * inversion H0. subst. exists []. split; auto. constructor.
  * inversion Cl1. inversion Cl2. subst. destruct H.
    rewrite <- Vrel_Fix_eq in H. rewrite <- Vrel_Fix_eq in H3.
    break_match_hyp; try congruence. break_match_hyp; try congruence.
    inversion H0. subst.
    apply (IHp1 l) in H. apply (IHp2 l0) in H3. all: auto.
    destruct H as [l11 [Hb Hbif]]. destruct H3 as [l12 [Hb2 Hbif2]].
    exists (l11 ++ l12). split; simpl. now rewrite Hb, Hb2.
    apply biforall_app; auto.
Qed.

Lemma nomatch_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  match_pattern p v1 = None -> match_pattern p v2 = None.
Proof.
  intros.
  assert (VALCLOSED v1) by (eapply Vrel_closed in H; apply H).
  assert (VALCLOSED v2) by (eapply Vrel_closed in H; apply H).
  generalize dependent v2. revert n. generalize dependent v1.
  induction p; destruct v1, v2; intros; try inversion_is_value; rewrite Vrel_Fix_eq in H; destruct H as [Cl1 [Cl2 H]]; try contradiction; simpl in H0; try congruence; auto.
  * break_match_hyp. congruence. simpl. subst. now rewrite Heqb.
  * break_match_hyp. congruence. simpl. subst. now rewrite Heqb.
  * inversion Cl1. inversion Cl2. subst. destruct H.
    rewrite <- Vrel_Fix_eq in H. rewrite <- Vrel_Fix_eq in H3.
    break_match_hyp; try congruence. break_match_hyp; try congruence.
    - simpl. eapply IHp2 in Heqo0. 3: exact H3. all: auto.
      rewrite Heqo0. break_match_goal; auto.
    - simpl. eapply IHp1 in Heqo. 3: exact H. all: auto.
      rewrite Heqo; auto.
Qed.

Lemma Erel_Case_compat_closed : forall n e1 e2 e1' e2' e3 e3' p,
    Erel n e1 e1' -> EXP pat_vars p ⊢ e2 -> EXP pat_vars p ⊢ e2' ->
    (forall m (Hmn : m <= n) vl vl', length vl = pat_vars p ->
        list_biforall (Vrel m) vl vl' -> 
                          Erel m e2.[list_subst vl idsubst ]
                                 e2'.[list_subst vl' idsubst])
    -> Erel n e3 e3' ->
    Erel n (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
  intros.
  destruct H, H3, H4, H5.
  split. 2: split. 1-2: constructor; auto.
  1-2: now rewrite Nat.add_0_r.
  intros. destruct H8, H10.
  inversion H9; subst; try inversion_is_value.
  epose proof (H6 k _ (FCase p e2 e3 ::F1) (FCase p e2' e3' ::F2) _ H18) as T.
  destruct T. exists (S x). constructor. auto.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; auto; now constructor.
  intros. assert (VALCLOSED v1) by (apply Vrel_closed in H12; apply H12).
  inversion H13; subst; try inversion_is_value.
  * eapply match_pattern_Vrel in H23 as H23_2. 2: exact H12.
    destruct H23_2 as [l2 [M2 Bif]].
    inversion H13; subst; try inversion_is_value. 2: congruence.
    rewrite H26 in H23. inversion H23. subst.
    apply match_pattern_length in H26 as H26_2.
    eapply biforall_impl in Bif. 2: intros; eapply Vrel_downclosed; exact H15.
    specialize (H2 k0 ltac:(lia) l l2 (eq_sym H26_2) Bif).
    destruct H2 as [Cl1 [Cl2 H2]]. eapply H2 in H27.
    destruct H27. exists (S x). eapply term_case_true; eauto.
    lia. split. 2: split. all: auto. intros. eapply H11. 3: exact H16. lia. auto.
  * eapply nomatch_pattern_Vrel in H23 as H23_2. 2: exact H12.
    inversion H13; subst; try inversion_is_value. congruence.
    eapply H7 in H24. destruct H24. exists (S x). apply term_case_false; eauto.
    lia. split. 2: split. all: auto. intros. eapply H11. 3: exact H16. lia. auto.
  Unshelve. lia.
Qed.

Lemma Erel_Var_compat :
  forall Γ n,
    n < Γ ->
    Erel_open Γ (EVar n) (EVar n).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Var_compat : core.

Lemma Erel_FunId_compat :
  forall Γ n,
    n < Γ ->
    Erel_open Γ (EFunId n) (EFunId n).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_FunId_compat : core.

Lemma Erel_Lit_compat :
  forall Γ l,
    Erel_open Γ (ELit l) (ELit l).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Lit_compat : core.

Lemma Erel_Fun_compat :
  forall Γ (vl vl' : list Var) b b', length vl = length vl' ->
    Erel_open (S (length vl) + Γ) b b' ->
    Erel_open Γ (EFun vl b) (EFun vl' b').
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Fun_compat : core.

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
  unfold Erel, exp_rel. specialize (H 0 ltac:(lia) (ELit 0%Z) (ELit 0%Z) (Vrel_Lit_compat_closed 0 0%Z)) as H'.
  split. 2: split.
  * apply Erel_closed_l in H'. constructor; auto.
    apply subst_implies_scope_exp_1; auto.
  * apply Erel_closed_r in H'. constructor; auto.
    apply subst_implies_scope_exp_1; auto.
  * intros. destruct m0; inversion H2; try inversion_is_value. subst.
    destruct H0, H3. eapply H4 in H5. destruct H5. exists (S x0). constructor. exact H5.
    lia.

    apply Erel_closed_l in H' as e1H. apply subst_implies_scope_exp_1 in e1H.
    apply Erel_closed_r, subst_implies_scope_exp_1 in H' as e2H.
    destruct H1, H6.
    split. 2: split. 1-2: constructor; auto; now constructor.
    intros. assert (VALCLOSED v1) by (apply Vrel_closed in H8; apply H8). assert (VALCLOSED v2) by (apply Vrel_closed in H8; apply H8).
    inversion H9; subst. 2-6: inversion H10. eapply H in H18. destruct H18.
    exists (S x0). constructor. auto. exact H12. 2: exact H8. lia. lia.

    split. 2: split. all: auto. intros. eapply H7. 3: exact H15. lia. auto.
    inversion_is_value. inversion_is_value.
Qed.

Global Hint Resolve Erel_Let_compat_closed : core.


Lemma Erel_Let_compat :
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
  intros.
  do 2 rewrite subst_comp, substcomp_scons, substcomp_id_r. apply H0.
  apply Vrel_closed in H2 as v. destruct v.
  split. 2: split.
  1-2: intro; intros; destruct v; cbn; auto; apply H1; lia.
  intros. destruct x0; auto. simpl. destruct H1, H6. specialize (H7 x0 ltac:(lia)).
  break_match_goal. break_match_goal; auto. eapply Vrel_downclosed; eauto. lia.
  Unshelve. lia.
Qed.

Global Hint Resolve Erel_Let_compat : core.

Lemma Erel_LetRec_compat_closed :
  forall n f1 f2 vl1 vl2 (b b' e e' : Exp) m (Hmn : m <= n)
  (CL1 : EXP S (length vl1) ⊢ b) (CL1 : EXP S (length vl2) ⊢ b')
  (CL1 : EXP 1 ⊢ e) (CL1 : EXP 1 ⊢ e'),
    Erel m e.[EFun vl1 b/] e'.[EFun vl2 b'/]  ->
    Erel m (ELetRec f1 vl1 b e) (ELetRec f2 vl2 b' e').
Proof.
  intros.
  unfold Erel, exp_rel. split. 2: split.
  * constructor. rewrite Nat.add_0_r. auto. auto.
  * constructor. rewrite Nat.add_0_r. auto. auto.
  * intros. inversion H1; try inversion_is_value. subst.
    destruct H0, H2. eapply H in H8. destruct H8. exists (S x). constructor.
    exact H4. lia. split. 2: split. all: auto.
    intros. eapply H3 in H7. exact H7. lia. auto.
Qed.

Global Hint Resolve Erel_LetRec_compat_closed : core.


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
      + eapply Vrel_Fun_compat, Erel_Val_compat, Erel_open_closed in H0.
        2: exact H3. 2: auto.
        destruct H0. inversion H0. simpl in H8. exact H8.
      + apply H2. lia.
    - intro. intros. destruct v; simpl.
      + rewrite H in H0.
        eapply Vrel_Fun_compat, Erel_Val_compat, Erel_open_closed in H0.
        2: exact H4. 2: auto.
        destruct H0. inversion H7. simpl in H8. exact H8.
      + apply H4. lia.
    - intros. destruct x.
      + simpl. eapply Vrel_Fun_compat; eauto.
      + simpl. specialize (H5 x ltac:(lia)).
        break_match_goal. break_match_goal. all: try lia. eapply Vrel_downclosed; eauto.
Unshelve. lia.
Qed.

Global Hint Resolve Erel_LetRec_compat : core.

Lemma Erel_Cons_compat_closed :
  forall m e1 e1' e2 e2', Erel m e1 e1' -> Erel m e2 e2'
 ->
  Erel m (ECons e1 e2) (ECons e1' e2').
Proof.
  intros. destruct H, H0, H1, H2.
  split. 2: split. 1-2: constructor; auto.
  intros. destruct H5, H7.
  destruct m0. inversion H6. inversion H9.
  inversion H6; try inversion_is_value. subst.
  epose (H4 m0 _ (FCons1 e1 ::F1) (FCons1 e1' ::F2) _ H11).
  destruct t. exists (S x). constructor. auto.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros. assert (VALCLOSED v1) by (apply Vrel_closed in H9; apply H9).
  inversion H10; subst; try inversion_is_value.
  epose (H3 k _ (FCons2 v1 :: F1) (FCons2 v2 :: F2) _ H18). destruct t.
  exists (S x). econstructor; eauto.

  Unshelve. lia.
  split. 2: split.
  1-2: constructor; apply Vrel_closed in H9; destruct H9; auto; constructor; auto.
  intros. assert (VALCLOSED v0) by (apply Vrel_closed in H13; apply H13).
  inversion H14; subst; try inversion_is_value.
  eapply H8 in H24. destruct H24. exists (S x).
  constructor; eauto. lia.

  eapply Vrel_Cons_compat_closed.
  eapply Vrel_downclosed. eassumption.
  eapply Vrel_downclosed. eassumption.
  Unshelve. all: lia.
Qed.

Global Hint Resolve Erel_Cons_compat_closed : core.

Lemma Erel_Cons_compat :
  forall Γ v1 v1' v2 v2', Erel_open Γ v1 v1' -> Erel_open Γ v2 v2'
 ->
  Erel_open Γ (ECons v1 v2) (ECons v1' v2').
Proof.
  unfold Erel_open. intros. simpl. apply Erel_Cons_compat_closed; [apply H | apply H0]; auto.
Qed.

Global Hint Resolve Erel_Cons_compat : core.

Lemma Vrel_Fun_right : forall m v2 vl b,
  Vrel m (EFun vl b) v2 -> exists b' vl', length vl = length vl' /\ v2 = EFun vl' b'.
Proof.
  intros. rewrite Vrel_Fix_eq in H. destruct H, H0. destruct v2; try contradiction. break_match_hyp.
  apply Nat.eqb_eq in Heqb0.
  2: contradiction. do 2 eexists. split; eauto.
Qed.

Lemma Erel_App_compat_ind : forall hds hds' tl tl' F1 F2 k0 v1 v2 (* P1 P1' P2 P2' *),
  list_biforall (Erel k0) hds hds' ->
  list_biforall (Vrel k0) tl tl' ->
  Vrel k0 v1 v2 ->
  FSCLOSED F1 ->
  FSCLOSED F2 ->
  (forall m : nat, m <= k0 -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓)
->
  frame_rel k0 (fun (m' : nat) (_ : m' <= k0) => Vrel m') (FApp2 v1 (* P1 *) hds tl (* P2 *) :: F1)
  (FApp2 v2 (* P1' *) hds' tl' (* P2' *) :: F2).
Proof.
  induction hds; intros.
  * inversion H. subst. apply biforall_length in H0 as LEN.
    assert (list_biforall (Vrel k0) tl tl') as BF by auto.
    apply biforall_vrel_closed in H0 as [H0_1 H0_2]. split. 2: split.
    1-2: constructor; auto; constructor; auto; apply Vrel_closed in H1; apply H1.
    intros.
    inversion H5; subst.
    - inversion H0. inversion H7.
    - apply Vrel_Fun_right in H1 as v; destruct v as [e1 [vl1 [? ?]]]. subst.
      rewrite Vrel_Fix_eq in H1. destruct H1 as [VCL1 [VCL2 H1]].
      rewrite H6, Nat.eqb_refl in H1.
      epose proof (H1 k _ (tl ++ [v0]) (tl' ++ [v3]) _ _ _) as E.
      destruct E as [E1CL [E2CL ?]]. eapply H7 in H14.
      destruct H14. exists (S x). constructor.
      + exact H0_2.
      + lia.
      + apply Vrel_closed in H0; apply H0.
      + exact H8.
      + lia.
      + split. 2: split. all: auto. intros. eapply H4 in H11. exact H11. lia. auto.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
  * inversion H. subst.
    apply biforall_length in H0 as LEN.
    apply biforall_vrel_closed in H0 as v. destruct v.
    apply biforall_erel_closed in H as v. destruct v.
    apply Vrel_closed in H1 as v. destruct v. split. 2: split.
    1-2: constructor; auto; now constructor.
    intros. inversion H14; subst.
    - inversion H13. inversion H16.
    - eapply H7 in H24. destruct H24. exists (S x). econstructor; auto.
      apply Vrel_closed in H13; apply H13.
      exact H15.
      lia.
      apply IHhds; auto.
      + inversion H. eapply biforall_impl in H25. exact H25. intros. eapply Erel_downclosed; eauto.
      + apply biforall_app. eapply biforall_impl in H0. exact H0. intros. eapply Vrel_downclosed; eauto.
        constructor. 2: constructor. eapply Vrel_downclosed; eauto.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H4 in H19. exact H19. lia. auto.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
Unshelve.
  all: auto; try lia.
  ** rewrite app_length. simpl. lia.
  ** rewrite app_length. simpl. lia.
  ** apply biforall_app.
    -- eapply biforall_impl in BF. exact BF. intros. eapply Vrel_downclosed; eauto.
    -- constructor. eapply Vrel_downclosed. eauto. constructor.
Unshelve. all: lia.
Qed.

Lemma Erel_App_compat_helper : forall es es' k F1 F2 (FCL1 : FSCLOSED F1) (FCL2 : FSCLOSED F2),
  (forall m : nat, m <= S k -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓) ->
  list_biforall (Erel k) es es' ->
  forall m, m <= k -> 
  forall v1 v2 : Exp, Vrel m v1 v2 -> | FApp1 es :: F1, v1 | m ↓ -> | FApp1 es' :: F2, v2 | ↓.
Proof.
  destruct es; intros.
  * apply biforall_length in H0 as L. apply eq_sym, length_zero_iff_nil in L. subst.
    inversion H3; subst.
    - inversion H2. inversion H5.
    - apply Vrel_Fun_right in H2 as v; destruct v as [e1 [vl1 [? ?]]].
      apply eq_sym, length_zero_iff_nil in H4. subst.
      rewrite Vrel_Fix_eq in H2. destruct H2 as [VCL1 [VCL2 ?]].
      rewrite Nat.eqb_refl in H2.
      specialize (H2 k0 ltac:(lia) [] [] (eq_refl _) (eq_refl _) ltac:(constructor)). simpl in H2.
      destruct H2 as [ECL1 [ECL2 ?]]. eapply H2 in H5.
      destruct H5. exists (S x). constructor. eauto. lia. split. 2: split. all: auto.
      intros. eapply H. 2: exact H4. lia. auto.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion_is_value.
    - inversion H2. inversion_is_value.
  * inversion H3; subst.
    - inversion H2. inversion H5.
    - inversion H0. subst.
      destruct H6 as [ECL1 [ECL2 ?]]. eapply H4 in H10. destruct H10. exists (S x).
      econstructor. apply Vrel_closed in H2; apply H2. exact H5. lia. apply Vrel_closed in H2 as v. destruct v.
      eapply Erel_App_compat_ind; auto.
      + eapply biforall_impl in H8; eauto. intros. eapply Erel_downclosed; eauto.
      + constructor.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H in H12; eauto. lia.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion_is_value.
    - inversion H2. inversion_is_value.
Unshelve.
  auto. all: lia.
Qed.

Lemma Erel_App_compat_closed :
  forall n e es e' es',
  Erel n e e' -> list_biforall (Erel n) es es'
->
  Erel n (EApp e es) (EApp e' es').
Proof.
  intros. destruct H, H1. split. 2: split.
  1-2: constructor; auto; rewrite <- indexed_to_forall; apply biforall_erel_closed in H0; apply H0.

 (* eval e *)
  intros. inversion H4; try inversion_is_value. subst.
  intros. eapply H2 in H9. destruct H9. exists (S x). constructor. exact H5. lia.
  destruct H3, H5. split. 2: split. 1-2: constructor; auto.
  1-2: constructor; apply biforall_erel_closed in H0; apply H0.

 (* eval es *)
  
  intros. eapply Erel_App_compat_helper in H8. exact H8. all: auto.
  intros. eapply H6 in H12; eauto. lia.
  eapply biforall_impl in H0. exact H0. intros. eapply Erel_downclosed; eauto.
Unshelve. lia.
Qed.

Global Hint Resolve Erel_App_compat_closed : core.

Lemma Erel_App_compat :
  forall Γ e es e' es',
  Erel_open Γ e e' -> list_biforall (Erel_open Γ) es es'
->
  Erel_open Γ (EApp e es) (EApp e' es').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_App_compat_closed; auto.
  eapply biforall_map; eauto.
Qed.

Global Hint Resolve Erel_App_compat : core.

Lemma Erel_Plus_compat : forall Γ e1 e2 e1' e2',
    Erel_open Γ e1 e1' -> Erel_open Γ e2 e2' ->
    Erel_open Γ (EPlus e1 e2) (EPlus e1' e2').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_Plus_compat_closed; auto.
Qed.

Global Hint Resolve Erel_Plus_compat : core.

Lemma Erel_Case_compat : forall Γ e1 e2 e1' e2' e3 e3' p,
    Erel_open Γ e1 e1' -> Erel_open (pat_vars p + Γ) e2 e2' -> Erel_open Γ e3 e3' ->
    Erel_open Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
  intros.
  unfold Erel_open.
  intros. cbn.
  eapply Erel_Case_compat_closed; auto.
  * apply Erel_open_scope_l in H0. apply -> subst_preserves_scope_exp. exact H0.
    rewrite <- (Nat.add_0_r (pat_vars p)) at 2. apply upn_scope. apply H2.
  * apply Erel_open_scope_r in H0. apply -> subst_preserves_scope_exp. exact H0.
    rewrite <- (Nat.add_0_r (pat_vars p)) at 2. apply upn_scope. apply H2.
  * intros.
    rewrite <- H3. apply biforall_length in H4 as H4'.
    rewrite subst_comp, substcomp_list, substcomp_id_r.
    rewrite H4'.
    rewrite subst_comp, substcomp_list, substcomp_id_r. apply H0.
    rewrite <- H3. apply Grel_list; auto. eapply Grel_downclosed. exact H2.
 Unshelve. lia.
Qed.

Global Hint Resolve Erel_Case_compat : core.

(** TODO: will be changed in the future: *)
Lemma Erel_ConcBIF_compat_closed :
  forall p1 p2 e1 e2 n, EXPCLOSED (EConcBIF p1 e1) -> EXPCLOSED (EConcBIF p2 e2) ->
(*   Erel n e1 e2 -> Erel n p1 p2 -> *)
  Erel n (EConcBIF p1 e1) (EConcBIF p2 e2).
Proof.
  intros. unfold Erel, exp_rel. split. 2: split.
  1-2: auto.
  intros. inversion H; subst; try inversion_is_value.
  apply ConcBIF_nonterminating in H2; auto. contradiction.
  now apply indexed_to_forall in H6.
Qed.

(** TODO: will be changed in the future: *)
Lemma Erel_ConcBIF_compat :
  forall p1 p2 e1 e2 Γ,
  EXP Γ ⊢ EConcBIF p1 e1 -> EXP Γ ⊢ EConcBIF p2 e2 ->
  Erel_open Γ (EConcBIF p1 e1) (EConcBIF p2 e2).
Proof.
  intros. unfold Erel_open. intros. simpl. apply Erel_ConcBIF_compat_closed; auto.
  replace (EConcBIF p1.[ξ₁] (map (subst ξ₁) e1)) with
          ((EConcBIF p1 e1).[ξ₁]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
  replace (EConcBIF p2.[ξ₂] (map (subst ξ₂) e2)) with
          ((EConcBIF p2 e2).[ξ₂]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
Qed.

Global Hint Resolve Erel_ConcBIF_compat : core.

(** TODO: will be changed in the future: *)
Lemma Erel_Receive_compat_closed :
  forall l1 l2 n,
  (* Erel n e1 e2 -> *)
  EXPCLOSED (EReceive l1) -> EXPCLOSED (EReceive l2) ->
  Erel n (EReceive l1) (EReceive l2).
Proof.
  intros. unfold Erel, exp_rel. split. 2: split.
  1-2: auto.
  intros. inversion H2; subst; try inversion_is_value.
Qed.

(** TODO: will be changed in the future: *)
Lemma Erel_Receive_compat :
  forall l1 l2 Γ,
  (* Erel_open Γ e1 e2 -> *)
  EXP Γ ⊢ EReceive l1 -> EXP Γ ⊢ EReceive l2 ->
  Erel_open Γ (EReceive l1) (EReceive l2).
Proof.
  intros. unfold Erel_open. intros. simpl. apply Erel_Receive_compat_closed; auto.
  replace (EReceive (map (fun '(p, v) => (p, v.[upn (pat_vars p) ξ₁])) l1)) with
          ((EReceive l1).[ξ₁]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
  replace (EReceive (map (fun '(p, v) => (p, v.[upn (pat_vars p) ξ₂])) l2)) with
          ((EReceive l2).[ξ₂]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
Qed.

Global Hint Resolve Erel_Receive_compat : core.

Theorem Erel_Vrel_Fundamental_helper :
  forall (e : Exp),
    (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
    (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e).
Proof.
  induction e using Exp_ind2 with
   (Q := fun l => Forall (fun e => (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
                                   (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e)) l)
   (W := fun l => Forall (fun '(_,e) => (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
                                   (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e)) l);
  intuition auto; try inversion_is_value.
  * apply Erel_Val_compat, Vrel_Var_compat. inversion H. now inversion H0.
  * apply Vrel_Var_compat. now inversion H.
  * apply Erel_Val_compat, Vrel_FunId_compat. inversion H. now inversion H0.
  * apply Vrel_FunId_compat. now inversion H.
  * apply Erel_Val_compat, Vrel_Fun_compat; auto. apply H. inversion H1. now inversion H2.
  * apply Vrel_Fun_compat; auto. apply H. now inversion H1.
  * inversion H1. subst. 2: inversion H2. apply Erel_App_compat. apply H. auto.
    apply forall_biforall_refl. apply Forall_and_inv in IHe0. destruct IHe0.
    assert (Forall (fun x : Exp => Erel_open Γ x x) el). {
      rewrite <- indexed_to_forall in H5.
      clear H H0 H1 H4 H3. induction el; constructor.
      * inversion H2. inversion H5. subst. apply H1. auto.
      * inversion H2. inversion H5. subst. apply IHel; auto.
    } auto.
  * inversion H3. subst. 2: inversion H4. apply Erel_Let_compat. now apply H. now apply H1.
  * inversion H3. subst. 2: inversion H4. apply Erel_LetRec_compat. auto. now apply H. now apply H1.
  * inversion H3. subst. 2: inversion H4. apply Erel_Plus_compat. now apply H. now apply H1.
  * inversion H5. subst. 2: inversion H6. apply Erel_Case_compat. now apply H. now apply H1. now apply H3.
  * inversion H3. subst. 2: inversion H4. apply Erel_Cons_compat. now apply H. now apply H1.
  * inversion H3. inversion H4. subst. apply Erel_Val_compat.
    apply Vrel_Cons_compat. now apply H0. now apply H2.
  * inversion H3. subst. apply Vrel_Cons_compat. now apply H0. now apply H2.
Qed.

Theorem Erel_Fundamental :
  forall (e : Exp) (Γ : nat),
    EXP Γ ⊢ e ->
    Erel_open Γ e e.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Global Hint Resolve Erel_Fundamental : core.

Theorem Vrel_Fundamental :
  forall (v : Exp) (Γ : nat),
    VAL Γ ⊢ v ->
    Vrel_open Γ v v.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Global Hint Resolve Vrel_Fundamental : core.

Lemma Grel_ids : forall n, Grel n 0 idsubst idsubst.
Proof.
  intros.
  unfold Grel.
  intuition auto using scope_idsubst.
  exfalso; auto. inversion H.
Qed.

Theorem Vrel_Fundamental_closed :
  forall (v : Exp),
    VALCLOSED v ->
    forall n, Vrel n v v.
Proof.
  intros.
  replace v with (v.[idsubst]).
  eapply Vrel_Fundamental; eauto using Grel_ids. apply idsubst_is_id.
Qed.

Global Hint Resolve Vrel_Fundamental_closed : core.

Theorem Erel_Fundamental_closed :
  forall (e : Exp),
    EXPCLOSED e ->
    forall n, Erel n e e.
Proof.
  intros.
  replace e with (e.[idsubst]).
  eapply Erel_Fundamental; eauto using Grel_ids.
  apply idsubst_is_id.
Qed.

Global Hint Resolve Erel_Fundamental_closed : core.

Theorem Grel_Fundamental :
  forall (ξ : Substitution) (Γ : nat),
    SUBSCOPE Γ ⊢ ξ ∷ 0 ->
    forall n, Grel n Γ ξ ξ.
Proof.
  intros.
  unfold Grel.
  intuition. break_match_goal. apply Vrel_Fundamental_closed.
  specialize (H x H0). rewrite Heqs in H. auto.
  specialize (H x H0). rewrite Heqs in H. inversion H. 
Qed.

Global Hint Resolve Grel_Fundamental : core.

Lemma Frel_Case :
    forall n (e2 e2' e3 e3' : Exp) p (CL1 : EXP pat_vars p ⊢ e2) (CL2 : EXP pat_vars p ⊢ e2'),
    (forall m, m <= n -> forall vl1 vl2, length vl1 = pat_vars p -> list_biforall (Vrel m) vl1 vl2 -> Erel m e2.[list_subst vl1 idsubst] e2'.[list_subst vl2 idsubst]) ->
    (forall m, m <= n -> Erel m e3 e3') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCase p e2 e3::F1) (FCase p e2' e3'::F2).
Proof.
  intros. destruct H2, H3.
  specialize (H0 m H1) as H0'.
  apply Erel_closed in H0' as v. destruct v.
  split. 2: split. 1-2: constructor; auto; now constructor.
  intros.
  apply Vrel_closed in H7 as v. destruct v.
  inversion H8; subst; try inversion_is_value.
  * eapply match_pattern_Vrel in H18 as H18'. 2: apply H7. destruct H18' as [l2 [M2 Bif]].
    apply match_pattern_length in H18.
    eapply biforall_impl in Bif. 2: { intros; eapply Vrel_downclosed; exact H11. }
    specialize (H k ltac:(lia) l l2 (eq_sym H18) Bif) as [? [? ?]].
    eapply H12 in H19. destruct H19. exists (S x). eapply term_case_true; auto. exact M2.
    exact H13.
    lia. split; [ auto | split ]; auto. intros. eapply H4. 3: exact H14. lia. auto.
  * eapply nomatch_pattern_Vrel in H18 as H18'. 2: apply H7.
    destruct H0' as [? [? ?]]. eapply H13 in H19.
    destruct H19. exists (S x). apply term_case_false; auto. exact H14.
    lia. split; [ auto | split ]; auto. intros. eapply H4. 3: exact H15. lia. auto.
  Unshelve. lia.
Qed.

Lemma Frel_Plus_lhs :
    forall n (e2 e2' : Exp),
    (forall m, m <= n -> Erel m e2 e2') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FPlus1 e2::F1) (FPlus1 e2'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Erel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply H' in H15. destruct H15. exists (S x). econstructor. auto. exact H10. lia.

  split. 2: split. 1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H13 as v. destruct v.
  inversion H14; subst; try inversion_is_value.

  apply Vrel_possibilities in H13. destruct H13.
  2: { do 2 destruct H13.
    * destruct H13. congruence.
    * do 5 destruct H13. congruence.
    * destruct H13.
      do 5 destruct H13; congruence.
      destruct H13; congruence.
  }
  destruct H13, H13. subst.

  apply Vrel_possibilities in H6. destruct H6. 
  2: { do 2 destruct H6.
    * destruct H6. congruence.
    * do 5 destruct H6. congruence.
    * destruct H6.
      do 5 destruct H6; congruence.
      destruct H6; congruence.
  }
  destruct H6, H6. subst.

  inversion H13. inversion H6. eapply H3 in H22. subst. destruct H22. exists (S x).
  constructor. exact H18. lia. subst. eapply Vrel_Lit_compat_closed.
Qed.

Lemma Frel_Plus_rhs :
    forall n (v1 v1' : Exp),
    (forall m, m <= n -> Vrel m v1 v1') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FPlus2 v1::F1) (FPlus2 v1'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Vrel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor.
  intros. apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.

  apply Vrel_possibilities in H'. destruct H'.
  2: { do 2 destruct H10.
    * destruct H10. congruence.
    * do 5 destruct H10. congruence.
    * destruct H10.
      do 5 destruct H10; congruence.
      destruct H10; congruence.
  }
  do 2 destruct H10. subst.

  apply Vrel_possibilities in H6. destruct H6. 
  2: { do 2 destruct H6.
    * destruct H6. congruence.
    * do 5 destruct H6. congruence.
    * destruct H6.
      do 5 destruct H6; congruence.
      destruct H6; congruence.
  }
  destruct H6, H6. subst.

  eapply H3 in H14. destruct H14. exists (S x1). 
  inversion H6. inversion H10. subst.
  constructor. exact H11. lia.
  inversion H6. inversion H10. apply Vrel_Lit_compat_closed.
Qed.

Lemma Frel_Let :
    forall n (e2 e2' : Exp) x x',
    (forall m v1 v2, m <= n -> Vrel m v1 v2 -> Erel m (e2.[v1/]) (e2'.[v2/])) ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FLet x e2::F1) (FLet x' e2'::F2).
Proof.
  intros. destruct H1, H2.
  specialize (H m (ELit 0%Z) (ELit 0%Z) H0 ltac:(auto)) as H'.
  apply Erel_closed in H' as v. destruct v.
  apply subst_implies_scope_exp_1 in H4. apply subst_implies_scope_exp_1 in H5.
  split. 2: split. 1-2: constructor; auto; now constructor.
  intros. apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply (H k) in H16. destruct H16. exists (S x0). constructor. auto.
  exact H10. lia. eapply Vrel_downclosed. eauto. lia.

  split. 2: split. 1-2: easy. intros.
  eapply H3 in H13. exact H13. lia. auto.
Unshelve. lia.
Qed.

Lemma Frel_App1 :
    forall n (es es' : list Exp),
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp1 es::F1) (FApp1 es'::F2).
Proof.
  intros. destruct H1, H2. split. 2: split.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * intros. destruct (Vrel_closed H4).
    inversion H5; subst; try inversion_is_value.
    - inversion H. subst. eapply H11 in H13. destruct H13. exists (S x).
      econstructor. auto. exact H8. exact H0. lia.
      apply Erel_App_compat_ind; auto.
      + eapply biforall_impl. 2: exact H14. intros. eapply H12. lia.
      + constructor.
      + eapply Vrel_downclosed. eauto.
      + intros. eapply H3 in H16. exact H16. lia. auto.
    - inversion H. subst. apply Vrel_Fun_right in H4 as v. destruct v, H8, H8.
      apply eq_sym, length_zero_iff_nil in H8. subst.
      rewrite Vrel_Fix_eq in H4. destruct H4, H8.
      rewrite Nat.eqb_refl in H9.
      specialize (H9 k ltac:(lia) [] [] (eq_refl _) (eq_refl _) ltac:(constructor)).
      eapply H9 in H12. destruct H12.
      exists (S x0). constructor. exact H10. lia.

      split. 2: split. 1-2: auto. intros. eapply H3 in H14. exact H14.
      lia. auto.
Unshelve. auto.
Qed.

Lemma Frel_App2 :
    forall n (es es' : list Exp) v1 v1' vs vs',
    (forall m, m <= n -> Vrel m v1 v1') ->
    list_biforall (fun v1 v2 => forall m, m <= n -> Vrel m v1 v2) vs vs' ->
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp2 v1 es vs::F1) 
                                                     (FApp2 v1' es' vs'::F2).
Proof.
  intros. destruct H3, H4.
  apply Erel_App_compat_ind.
  * eapply biforall_impl. 2: exact H1. intros. now apply H6.
  * eapply biforall_impl. 2: exact H0. intros. now apply H6.
  * now apply H.
  * easy.
  * easy.
  * intros. eapply H5 in H8. exact H8. lia. auto.
Qed.

Lemma Frel_Cons_tail :
    forall n (e2 e2' : Exp),
    (forall m, m <= n -> Erel m e2 e2') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons1 e2::F1) (FCons1 e2'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Erel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply H' in H15. destruct H15. exists (S x). econstructor. auto. exact H10. lia.

  split. 2: split. 1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H13 as v. destruct v.
  inversion H14; subst; try inversion_is_value.

  eapply H3 in H24. subst. destruct H24. exists (S x).
  constructor; auto. exact H18. lia. subst. eapply Vrel_Cons_compat_closed.
  eapply Vrel_downclosed; eassumption.
  eapply Vrel_downclosed; eassumption.
Unshelve. all: lia.
Qed.

Lemma Frel_Cons_head :
    forall n (v1 v1' : Exp),
    (forall m, m <= n -> Vrel m v1 v1') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons2 v1::F1) (FCons2 v1'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Vrel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply H3 in H16. 2: lia. destruct H16. exists (S x).
  econstructor; auto. exact H10.

  eapply Vrel_Cons_compat_closed.
  eapply Vrel_downclosed; eassumption.
  eapply Vrel_downclosed; eassumption.
Unshelve. all: lia.
Qed.

Theorem Frel_Fundamental_closed :
  forall (F : FrameStack) (n : nat),
    FSCLOSED F ->
    Frel n F F.
Proof.
  induction F; intros.
  * cbn. split. 2: split. 1-2: constructor. intros.
    exists 0. constructor. apply Vrel_closed in H0; apply H0.
  * split. 2: split. all: auto. intros. destruct a; inversion H; inversion H4.
    - eapply Frel_App1; eauto. subst. eapply forall_biforall_refl, Forall_impl.
      2: exact H7. intros. auto.
    - eapply Frel_App2; eauto; subst.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H11. intros. auto.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H10. intros. auto.
    - eapply Frel_Let; eauto.
      intros. subst. eapply Erel_Fundamental; eauto. unfold Grel.
      destruct (Vrel_closed H10). split. 2: split.
      1-2: apply cons_scope; auto.
      intros. inversion H6; subst. 2: inversion H11. simpl. auto.
    - eapply Frel_Plus_lhs; eauto.
    - eapply Frel_Plus_rhs; eauto.
    - eapply Frel_Case; eauto.
      intros. subst. eapply Erel_Fundamental; eauto.
      rewrite <- H12. eapply (Grel_list _ _ _ _ _ 0) in H13.
      rewrite Nat.add_0_r in H13. exact H13. apply Grel_Fundamental.
      apply scope_idsubst.
    - eapply Frel_Cons_tail; eauto.
    - eapply Frel_Cons_head; eauto.
    - assert (| F, EConcBIF v1 l | S m ↓) by now constructor.
      apply Vrel_closed_l in H0.
      apply ConcBIF_nonterminating in H8; auto. contradiction. now constructor.
    - subst. apply Vrel_closed_l in H0.
      eapply ConcBIF_nonterminating_helper in H1; auto. contradiction.
      intros. eapply term_eval; eauto.
Qed.

Global Hint Resolve Frel_Fundamental_closed : core.

