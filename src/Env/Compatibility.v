(**
  This file records the compatibility statements for CIU and CIU_open in the
  environment-based semantics.

  The statements mirror the role played by the compatibility lemmas for logical
  relations in [src/Compatibility.v], but are adapted to the env syntax and the
  concrete-environment form of [Env.CIU].
 *)

From CoreErlang Require Export Env.CIU.

Import ListNotations.

Inductive cons1_frame_rel (Γ : Env) (e1 e1' : Exp) : FrameStack -> FrameStack -> Prop :=
| cons1_here Fs :
    cons1_frame_rel Γ e1 e1' (FCons1 e1 Γ :: Fs) (FCons1 e1' Γ :: Fs)
| cons1_skip f Fs Fs' :
    cons1_frame_rel Γ e1 e1' Fs Fs' ->
    cons1_frame_rel Γ e1 e1' (f :: Fs) (f :: Fs').

Theorem CIU_Var_compat_closed :
  forall Γ n,
    ENVCLOSED Γ ->
    n < length Γ ->
    CIU Γ (EVar n) (EVar n).
Proof.
  intros Γ n HΓ Hn.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Var_compat :
  forall Γ n,
    n < Γ ->
    CIU_open Γ (EVar n) (EVar n).
Proof.
  intros Γ n Hn Γ' Hlen Hclosed.
  apply CIU_Var_compat_closed.
  - exact Hclosed.
  - lia.
Qed.

Theorem CIU_Lit_compat_closed :
  forall Γ l,
    ENVCLOSED Γ ->
    CIU Γ (˝ (VLit l)) (˝ (VLit l)).
Proof.
  intros Γ l HΓ.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Lit_compat :
  forall Γ l,
    CIU_open Γ (˝ (VLit l)) (˝ (VLit l)).
Proof.
  intros Γ l Γ' Hlen Hclosed.
  apply CIU_Lit_compat_closed.
  exact Hclosed.
Qed.

Theorem CIU_Pid_compat_closed :
  forall Γ p,
    ENVCLOSED Γ ->
    CIU Γ (˝ (VPid p)) (˝ (VPid p)).
Proof.
  intros *. repeat split.
  * auto.
  * do 2 constructor.
  * do 2 constructor.
  * intros. assumption.
Qed.

Theorem CIU_Pid_compat :
  forall Γ p,
    CIU_open Γ (˝ (VPid p)) (˝ (VPid p)).
Proof.
  intros * HΓ Hlen Hclosed.
  apply CIU_Pid_compat_closed.
  auto.
Qed.

Theorem CIU_Nil_compat_closed :
  forall Γ,
    ENVCLOSED Γ ->
    CIU Γ (˝ VNil) (˝ VNil).
Proof.
  intros Γ HΓ.
  unfold CIU. repeat split.
  - exact HΓ.
  - by do 2 constructor.
  - by do 2 constructor.
  - intros. assumption.
Qed.

Theorem CIU_Nil_compat :
  forall Γ,
    CIU_open Γ (˝ VNil) (˝ VNil).
Proof.
  intros Γ Γ' Hlen Hclosed.
  apply CIU_Nil_compat_closed.
  exact Hclosed.
Qed.

Theorem CIU_Cons_compat_closed :
  forall Γ e1 e1' e2 e2',
    CIU Γ e1 e1' ->
    CIU Γ e2 e2' ->
    CIU Γ (ECons e1 e2) (ECons e1' e2').
Proof.
  intros * [H1Γ [H1_1 [H1_2 HD1]]] [H2Γ [H2_1 [H2_2 HD2]]].
  repeat split.
  * assumption.
  * by do 2 constructor.
  * by do 2 constructor.
  * intros * HF D. destruct D as [k0 D]. inv D. apply ex_intro with (x := k) in H4.
    eapply HD2 in H4. 2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct H4 as [i D].
    eapply term_eval_empty in D as D'; eauto.
    2: by apply exp_to_any.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct D' as [v [l [Γ' [Hv D']]]].
    eapply frame_indep_core in D' as D''.
    eapply terminates_step_any_2 in D. 2: exact D''. clear D''. inv D.
    apply ex_intro with (x := k0)in H1. eapply HD1 in H1.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct H1 as [j D].
    eapply term_eval_empty in D as D'''; eauto.
    2: by apply exp_to_any.
    2: {
      constructor; auto.
      constructor; assumption.
    }
    destruct D''' as [v2 [l2 [Γ'2 [Hv2 D'2]]]].
    eapply frame_indep_core in D'2 as D''2.
    eapply terminates_step_any_2 in D. 2: exact D''2. clear D''2.
    inv D.
    eexists. constructor.
    eapply step_term_term_plus. eapply frame_indep_core in D'. exact D'.
    constructor.
    eapply step_term_term_plus. eapply frame_indep_core in D'2. exact D'2.
    constructor.
    exact H1.
Qed.

Theorem CIU_Cons_compat :
  forall Γ e1 e1' e2 e2',
    CIU_open Γ e1 e1' ->
    CIU_open Γ e2 e2' ->
    CIU_open Γ (ECons e1 e2) (ECons e1' e2').
Proof.
  intros * He1 He2 HΓ Hlen Hclosed.
  apply CIU_Cons_compat_closed.
  * apply He1; auto.
  * apply He2; auto.
Qed.

Corollary step_terminates_any :
  forall Γ fs e k Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓ ->
      | Γ, fs, e | ↓.
Proof.
  intros * H H'.
  destruct H'. exists (k + x).
  eapply step_term_term.
  * eassumption.
  * rewrite Nat.add_sub'. assumption.
  * lia.
Qed.

Corollary step_terminates_one :
  forall Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓ ->
      | Γ, fs, e | ↓.
Proof.
  intros * H H'.
  eapply step_terminates_any with (k := 1).
  * eapply step_trans.
    + eauto.
    + apply step_refl.
  * auto.
Qed.

Corollary terminates_step_one :
  forall Γ fs e Γ' fs' e',
    | Γ, fs, e | ↓ ->
      ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓.
Proof.
  intros * HT H1.
  Check terminates_step_any.
  eapply terminates_step_any with (k := 1).
  eauto. econstructor. eauto. constructor.
Qed.

Require Import Stdlib.Program.Equality.

Lemma VCons_term_forwards : 
  forall Γ Fs v1 v2,
    | Γ, Fs, ECons (˝v1) (˝v2) | ↓ ->
    | Γ, Fs, VCons v1 v2 | ↓.
Proof.
  intros * D.
  eapply terminates_step_one in D. 2:constructor.
  eapply terminates_step_one in D. 2:constructor.
  eapply terminates_step_one in D. 2:constructor.
  auto.
Qed.

Lemma VCons_term_backwards :
  forall Γ Fs v1 v2,
    | Γ, Fs, VCons v1 v2 | ↓ ->
    | Γ, Fs, ECons (˝v1) (˝v2) | ↓.
Proof.
  intros * D.
  eapply step_terminates_one. 1:constructor.
  eapply step_terminates_one. 1:constructor.
  eapply step_terminates_one. 1:constructor.
  auto.
Qed.

Theorem CIU_VCons_compat_closed :
  forall Γ v1 v1' v2 v2',
    CIU Γ (˝v1) (˝v1') ->
    CIU Γ (˝v2) (˝v2') ->
    CIU Γ (VCons v1 v2) (VCons v1' v2').
Proof.
  intros * HCIU1 HCIU2.
  repeat split.
  * destruct HCIU1 as [HΓ _]. auto.
  * destruct HCIU1 as [_ [Hlv1 _]].
    destruct HCIU2 as [_ [Hlv2 _]].
    do 2 constructor.
    + inv Hlv1; auto.
    + inv Hlv2; auto.
  * destruct HCIU1 as [_ [_ [Hlv1' _]]].
    destruct HCIU2 as [_ [_ [Hlv2' _]]].
    do 2 constructor.
    + inv Hlv1'; auto.
    + inv Hlv2'; auto.
  * intros * HFs D.
    apply VCons_term_forwards.
    apply VCons_term_backwards in D.
    revert Fs HFs D.
    apply proj2 with (A := EXP length Γ ⊢ ECons (˝v1') (˝v2')).
    apply proj2 with (A := EXP length Γ ⊢ ECons (˝v1) (˝v2)).
    apply proj2 with (A := ENVCLOSED Γ).
    (* fold (CIU Γ (ECons (˝ v1) (˝ v2)) (ECons (˝ v1') (˝ v2'))). *)
    apply CIU_Cons_compat_closed.
    all: auto.
Qed.

Theorem CIU_VCons_compat :
  forall Γ v1 v2 v1' v2',
  CIU_open Γ (˝v1) (˝v1') ->
  CIU_open Γ (˝v2) (˝v2') ->
  CIU_open Γ (VCons v1 v2) (VCons v1' v2').
Proof.
  intros * Ho1 Ho2 Γ Hlen Hclosed.
  apply CIU_VCons_compat_closed.
  + apply Ho1; auto.
  + apply Ho2; auto.
Qed.

Theorem CIU_Clos_compat :
  forall Γ Γ' vl b1 b2,
  CIU_open (S vl + length Γ) b1 b2 ->
  ENVCLOSED Γ ->
  CIU_open Γ' (VClos Γ vl b1) (VClos Γ vl b2).
Proof.
  intros * Ho.
  unfold CIU_open in *.
  repeat split.
  * auto.
  * apply CIU_open_scope_l in Ho as Ho'.
    do 2 constructor.
    2: auto.
    intros * Hi.
    apply ENVCLOSED_nth; auto.
  * apply CIU_open_scope_r in Ho as Ho'.
    do 2 constructor.
    2: auto.
    intros * Hi.
    apply ENVCLOSED_nth; auto.
  * intros * HFs D.
    unfold CIU in Ho.
    destruct Fs.
    + exists 0. constructor.
    + destruct f.
      - destruct l.
        ** inv D. inv H2. simpl in H6.
           destruct vl; try discriminate. inv H6.
           eapply step_terminates_one. 1:constructor; reflexivity.
           simpl.
           apply Ho; auto.
           ++ constructor; auto. constructor.
              -- intros Hl. apply ENVCLOSED_nth. auto.
              -- apply CIU_open_scope_r in Ho as Hl. auto.
           ++ inv HFs. auto.
           ++ admit.
        ** admit.
      - destruct l.
        ** inv D. inv H2.
        ** eapply terminates_step_one in D. 2: constructor.
           eapply step_terminates_one. 1: constructor.
           destruct D as [k D].
           eapply term_eval_empty in D as D'.
           2: { inv HFs. inv H4. inv H6. apply exp_to_any. auto. }
           2: { inv HFs. constructor; auto. inv H4. constructor; auto.
                2: { inv H6. auto. }
                constructor.
                * intros *. apply ENVCLOSED_nth. auto.
                * apply CIU_open_scope_l in Ho. auto. }
           2: { inv HFs. inv H4. auto. }
           destruct D' as [v [k' [Γ'' [Hv D']]]].
           eapply frame_indep_core in D' as D''.
           eapply frame_indep_core in D'. simpl in D', D''.
           apply ex_intro with (x := k) in D.
           eapply terminates_step_any in D. 2: exact D'. clear D'.
           eapply step_terminates_any. 1: exact D''. clear D''.
           assert (ENVCLOSED []) by constructor.
           remember [] as Vldone.
           clear HeqVldone.
           generalize dependent Vldone.
           generalize dependent v.
           generalize dependent Γ''.
           induction l; intros.
           ++ inv D. inv H3.
           ++ eapply terminates_step_one in D. 2:constructor.
              eapply step_terminates_one. 1: constructor.
              destruct D as [k'' D].
              eapply term_eval_empty in D as D'.
              2: { inv HFs. inv H5. inv H7. inv H8. apply exp_to_any. auto. }
              2: { inv HFs. constructor; auto. inv H5. constructor; auto.
                   1: { constructor. intros. eapply ENVCLOSED_nth; auto.
                        apply CIU_open_scope_l in Ho. auto. }
                   1: { apply Forall_app. split; auto. }
                   1: { inv H7. inv H8. auto. } }
              2: { inv HFs. inv H5. auto. }
              destruct D' as [v' [k''' [Γ''' [Hv' D']]]].
              eapply frame_indep_core in D' as D''.
              eapply frame_indep_core in D'. simpl in D', D''.
              apply ex_intro with (x := k'') in D.
              eapply terminates_step_any in D. 2: exact D''. clear D''.
              eapply step_terminates_any. 1: exact D'. clear D'.
              eapply IHl; auto.
              -- inv HFs. constructor; auto. inv H5. inv H7. inv H8.
                 constructor; auto.
              -- apply ENVCLOSED_app; auto. constructor; auto.
      - admit.
      - destruct p.
        all:eapply terminates_step_one in D.
        6: apply red_case_true; reflexivity.
        2,4,7,9: apply red_case_false; reflexivity.
        all: eapply step_terminates_one.
        5: apply red_case_true; reflexivity.
        1,3,6,8: apply red_case_false; reflexivity.
        all: try auto.
        simpl in *. admit.
      - admit.
      - eapply terminates_step_one in D. 2:constructor.
        eapply step_terminates_one. 1:constructor. admit.
      - admit.
      - 
Admitted.

Theorem CIU_Fun_compat :
  forall Γ vl b b',
    CIU_open (S vl + Γ) b b' ->
    CIU_open Γ (EFun vl b) (EFun vl b').
Proof.
  intros * Ho Γ' Hl Hc.
  unfold CIU_open in Ho.
  repeat split.
  * auto.
  * rewrite Hl. constructor. constructor.
    specialize (Ho (repeat VNil (S vl) ++ Γ')).
    rewrite length_app in Ho.
    rewrite repeat_length in Ho.
    rewrite Hl in Ho.
    specialize (Ho eq_refl).
    assert (ENVCLOSED (repeat VNil (S vl) ++ Γ')).
    { apply ENVCLOSED_app; auto.
      clear. simpl. apply ENVCLOSED_cons; auto.
      induction vl.
      * simpl. constructor.
      * simpl. apply ENVCLOSED_cons; auto.
    }
    specialize (Ho H).
    destruct Ho as [_ [Hb _]].
    rewrite length_app in Hb.
    rewrite repeat_length in Hb.
    rewrite Hl in Hb. auto.
  * rewrite Hl. constructor. constructor.
    specialize (Ho (repeat VNil (S vl) ++ Γ')).
    rewrite length_app in Ho.
    rewrite repeat_length in Ho.
    rewrite Hl in Ho.
    specialize (Ho eq_refl).
    assert (ENVCLOSED (repeat VNil (S vl) ++ Γ')).
    { apply ENVCLOSED_app; auto.
      simpl. apply ENVCLOSED_cons; auto.
      clear. induction vl.
      * constructor.
      * simpl. constructor; auto. }
    specialize (Ho H).
    destruct Ho as [_ [_ [Hb _]]].
    rewrite length_app in Hb.
    rewrite repeat_length in Hb.
    rewrite Hl in Hb. auto.
  * intros * Hf D.
    eapply terminates_step_one in D. 2:constructor.
    eapply step_terminates_one. constructor.
    
    unfold CIU in Ho.
    
Admitted.

Theorem CIU_Let_compat_closed :
  forall Γ e1 e1' e2 e2',
    CIU Γ e1 e1' ->
    CIU_open (S (length Γ)) e2 e2' ->
    CIU Γ (ELet e1 e2) (ELet e1' e2').
Proof.
  intros * [H1Γ [H1en [H1len' H1closed]]] H2.
  assert (EXP S (length Γ) ⊢ e2 /\ EXP S (length Γ) ⊢ e2') as He2.
  {
    specialize (H2 (VNil :: Γ) eq_refl).
    assert (ENVCLOSED (VNil :: Γ)).
    { apply ENVCLOSED_cons. constructor. auto. }
    specialize (H2 H).
    destruct H2 as [_ [Hl [Hl' _]]]. simpl in Hl. split; assumption.
  }
  destruct He2 as [He2 He2'].
  repeat split.
  * assumption.
  * do 2 constructor; auto.
  * do 2 constructor; auto.
  * intros * Hf Ht.
    unfold CIU_open in H2.
    destruct Ht as [x Ht]. inv Ht. apply ex_intro with (x := k) in H5.
    apply H1closed in H5.
    2: { constructor; auto. constructor; auto. }
    clear k.
    destruct H5 as [i D].
    eapply term_eval_empty in D as D'; auto.
    2: by apply exp_to_any.
    2: { constructor; auto. constructor; auto. }
    destruct D' as [v [k [Γ' [Hv D']]]].
    eapply frame_indep_core in D' as D''.
    eapply terminates_step_any_2 in D. 2:eassumption.
    simpl in *. clear D''. inv D.
    apply ex_intro with (x := k0) in H1.
    specialize (H2 (v :: Γ) eq_refl).
    assert (ENVCLOSED (v :: Γ)).
    { constructor; auto. }
    specialize (H2 H). clear H.
    destruct H2 as [_ [_ [_ H2]]].
    apply H2 in H1; auto.
    destruct H1 as [k' D].
    eapply term_eval_empty in D as D''; auto.
    2: by apply exp_to_any.
    2: { constructor; auto. }
    destruct D'' as [v0 [k'' [Γ'' [Hv' D'']]]].
    eapply frame_indep_core in D''.
    eapply terminates_step_any_2 in D. 2:eassumption.
    simpl in *.
    eexists. constructor.
    eapply step_term_term_plus. eapply frame_indep_core in D'. exact D'.
    constructor.
    eapply step_term_term_plus. exact D''.
    eassumption.
Qed.

Theorem CIU_Let_compat :
  forall Γ e1 e1' e2 e2',
    CIU_open Γ e1 e1' ->
    CIU_open (S Γ) e2 e2' ->
    CIU_open Γ (ELet e1 e2) (ELet e1' e2').
Proof.
  intros * He1 He2 HΓ Hlen Hclosed.
  apply CIU_Let_compat_closed.
  * apply He1; auto.
  * rewrite Hlen. auto.
Qed.

Lemma CIU_list_biforall_scope :
  forall Γ vals1 vals2,
  list_biforall (CIU Γ) vals1 vals2 ->
  Forall (fun e => EXP length Γ ⊢ e) vals1 /\
  Forall (fun e => EXP length Γ ⊢ e) vals2.
Proof.
  intros * Hlbfa.
  apply indexed_to_biforall with (d1 := ˝VNil) (d2 := ˝VNil) in Hlbfa.
  destruct Hlbfa as [H H'].
  split.
  * apply List.Forall_forall.
    intros * Hin.
    apply In_nth with (d := ˝VNil) in Hin.
    destruct Hin as [n [Hl Hnth]].
    specialize (H n Hl).
    rewrite Hnth in H.
    unfold CIU in H.
    destruct H as [_ [HL _]]. assumption.
  * apply List.Forall_forall.
    intros * Hin.
    apply In_nth with (d := ˝VNil) in Hin.
    destruct Hin as [n [Hl Hnth]].
    rewrite H' in H.
    specialize (H n Hl).
    rewrite Hnth in H.
    destruct H as [_ [_ [HL _]]]. assumption.
Qed.

Theorem CIU_App_compat_closed :
  forall Γ f1 f2 vals1 vals2,
    CIU Γ f1 f2 ->
    list_biforall (CIU Γ) vals1 vals2 ->
    CIU Γ (EApp f1 vals1) (EApp f2 vals2).
Proof.
  intros * [HΓ [Hlf1 [Hlf2 HD]]] Hlbfa.
  apply CIU_list_biforall_scope in Hlbfa as Hl.
  destruct Hl as [Hlv1 Hlv2].
  repeat split.
  * auto.
  * do 2 constructor; auto.
    intros i Hleni.
    eapply indexed_to_forall in Hlv1.
    + exact Hlv1.
    + exact Hleni.
  * do 2 constructor; auto.
    intros i Hleni.
    eapply indexed_to_forall in Hlv2.
    + exact Hlv2.
    + exact Hleni.
  * intros * HF D.
    destruct D as [k D'].
    inv D'. apply ex_intro with (x := k0) in H4.
    eapply HD in H4.
    2: { constructor; auto. constructor; auto. }
    clear k0. destruct H4 as [k D].
    apply term_eval_empty in D as D'; auto.
    2: by apply exp_to_any.
    2: repeat constructor; auto.
    destruct D' as [v [k' [Γ' [Hv D']]]].
    eapply step_terminates_one. constructor.
    eapply frame_indep_core in D' as D''. simpl in D''.
    eapply step_terminates_any. eauto. clear D''.
    eapply frame_indep_core in D'. simpl in D'.
    apply ex_intro with (x := k) in D.
    eapply terminates_step_any in D. 2:eassumption. clear D'.
    clear f1 f2 Hlf1 Hlf2 HD.
    apply indexed_to_biforall with (d1 := ˝VNil)  (d2 := ˝VNil) in Hlbfa.
    destruct Hlbfa as [Hlbfa1 Hlbfa2].
    
    destruct vals1.
    + simpl in Hlbfa2. symmetry in Hlbfa2.
      apply length_zero_iff_nil in Hlbfa2. subst vals2.
      assumption.
    + destruct vals2; try discriminate.
      inv D. inv H.
      eapply step_terminates_one. constructor.
      remember Hlbfa1 as Hlbfa1'. clear HeqHlbfa1'.
      specialize (Hlbfa1' 0 (Nat.lt_0_succ _)).
      simpl in Hlbfa1'.
      destruct Hlbfa1' as [_ [_ [He0 HD]]].
      apply ex_intro with (x := k0) in H7.
      apply HD in H7 as D.
      2: { constructor; auto. constructor; auto.
           apply Forall_inv_tail in Hlv1. auto. }
      clear HD.
      destruct D as [k'' D].
      apply term_eval_empty in D as D'; auto.
      2: by apply exp_to_any.
      2: { constructor; auto. constructor; auto.
           apply Forall_inv_tail in Hlv1. auto. }
      destruct D' as [v' [k''' [Γ'' [Hv' D']]]].
      eapply frame_indep_core in D' as D''.
      eapply frame_indep_core in D'.
      eapply step_terminates_any. exact D''. clear D''.
      apply ex_intro with (x := k'') in D.
      eapply terminates_step_any in D. 2: exact D'. clear D'.
      simpl. simpl in D. clear H7 He0.

      remember [] as evd.
      assert (Forall (fun v => VALCLOSED v) evd).
      { subst. auto. }
      clear Heqevd.
      generalize dependent vals2.
      generalize dependent evd.
      generalize dependent v'.
      revert Γ'' v Hv.
      
      induction vals1.
      - intros Γ'' v Hv v' Hv' evd D Hevd vals2 HD Hl Hlv2. destruct vals2; try discriminate.
        specialize (HD 0 (Nat.lt_0_succ _)).
        destruct HD as [_ [_ [_ HD]]].
        simpl in HD.
        assumption.
      - intros Γ'' v Hv v' Hv' evd D Hevd vals2 HD Hl Hlv2. destruct vals2; try discriminate.
        remember HD as HD'. clear HeqHD'.
        remember HD as HDFINAL. clear HeqHDFINAL.
        specialize (HD' 0). assert (0 < length (e :: a :: vals1)) as H. simpl. lia.
        specialize (HD' H). clear H. simpl in HD'.
        destruct HD' as [_ [_ [He0 HD']]].
        
        apply Forall_cons_1 in Hlv1.
        destruct Hlv1 as [Hlv1' Hlv1''].
        apply Forall_inv_tail in Hlv1''.
        pose proof (Forall_cons_2 _ _ _ Hlv1' Hlv1'') as Hlv1.
        clear Hlv1' Hlv1''.
        specialize (IHvals1 Hlv1).
        specialize (HD 1). assert (1 < length (e :: a :: vals1)) as H. simpl. lia.
        specialize (HD H). clear H.
        simpl in HD.
        destruct HD as [_ [_ [He1 HD]]].
        
        eapply step_terminates_one. constructor.
        inv D. inv H. apply ex_intro with (x := k1) in H9.
        apply HD in H9.
        2: { constructor; auto. constructor; auto.
             apply Forall_app; auto.
             apply Forall_inv_tail in Hlv1. auto. }
        destruct H9 as [k2 D].
        apply term_eval_empty in D as D'; auto.
        2: by apply exp_to_any.
        2: { constructor; auto. constructor; auto.
             apply Forall_app; auto.
             apply Forall_inv_tail in Hlv1. auto. }
        destruct D' as [v'' [k3 [Γ1 [Hv'' D']]]].
        eapply frame_indep_core in D' as D''.
        eapply frame_indep_core in D'.
        simpl in D', D''.
        eapply step_terminates_any. exact D''. clear D''.
        apply ex_intro with (x := k2) in D.
        eapply terminates_step_any in D. 2: exact D'. clear D'.
        apply IHvals1; auto.
        ** apply Forall_app. auto.
        ** intros * Hl'. clear IHvals1.
           repeat split; auto.
           ++ eapply List.Forall_nth with (d := ˝ VNil) in Hlv1.
              2: exact Hl'.
              auto.
           ++ apply Forall_cons_1 in Hlv2.
              destruct Hlv2 as [Hlv2' Hlv2''].
              apply Forall_inv_tail in Hlv2''. 
              pose proof (Forall_cons_2 _ _ _ Hlv2' Hlv2''). clear Hlv2' Hlv2''.
              apply indexed_to_forall; auto.
              simpl. simpl in Hl'. rewrite <- Hl. auto.
           ++ intros * Hfs0 HDD.
              destruct i.
              -- simpl in HDD. simpl. apply HD'; auto.
              -- simpl in HDD. simpl.
                 simpl in Hl'.
                 apply Nat.succ_lt_mono in Hl'.
                 specialize (HDFINAL (S (S i))).
                 assert (S (S i) < length (e :: a :: vals1)) as Hl''. simpl. lia.
                 specialize (HDFINAL Hl''). clear Hl''.
                 simpl in HDFINAL.
                 destruct HDFINAL as [_ [_ [_ HDFINAL]]].
                 apply HDFINAL; assumption.
        ** apply Forall_cons_1 in Hlv2.
           destruct Hlv2 as [Hlv2' Hlv2''].
           apply Forall_inv_tail in Hlv2''. 
           pose proof (Forall_cons_2 _ _ _ Hlv2' Hlv2''). clear Hlv2' Hlv2''. auto.
Qed.

Theorem CIU_App_compat :
  forall Γ f1 f2 vals1 vals2,
    CIU_open Γ f1 f2 ->
    list_biforall (CIU_open Γ) vals1 vals2 ->
    CIU_open Γ (EApp f1 vals1) (EApp f2 vals2).
Proof.
  intros * Ho Hlbfa Γ0 Hlen Hclosed.
  apply CIU_App_compat_closed; auto.
  eapply indexed_to_biforall with (d1 := ˝VLit 0%Z) (d2 := ˝VLit 0%Z) in Hlbfa.
  eapply indexed_to_biforall with (d1 := ˝VLit 0%Z) (d2 := ˝VLit 0%Z).
  destruct Hlbfa.
  split; auto.
  intros i Hl.
  specialize (H i Hl).
  unfold CIU_open in H.
  specialize (H Γ0 Hlen Hclosed). auto.
Qed.

Theorem CIU_Case_compat_closed :
  forall Γ e1 e1' e2 e2' e3 e3' p,
    CIU Γ e1 e1' ->
    CIU_open (pat_vars p + length Γ) e2 e2' ->
    CIU Γ e3 e3' ->
    CIU Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
  intros * [HΓ [Hlen1 [Hlen1' HD1]]] Ho [_ [Hlen3 [Hlen3' HD3]]].
  unfold CIU_open in Ho.
  assert (EXP pat_vars p + length Γ ⊢ e2 /\ EXP pat_vars p + length Γ ⊢ e2').
  { specialize (Ho (repeat VNil (pat_vars p) ++ Γ)).
    rewrite length_app in Ho.
    rewrite repeat_length in Ho.
    specialize (Ho eq_refl).
    assert (ENVCLOSED (repeat VNil (pat_vars p) ++ Γ)).
    { apply ENVCLOSED_app; auto.
      remember (pat_vars p) as k. clear.
      induction k.
      * simpl. constructor.
      * simpl. constructor; auto. 
    }
    specialize (Ho H).
    destruct Ho as [_ [He2 [He2' _]]].
    rewrite length_app in He2, He2'.
    rewrite repeat_length in He2, He2'.
    split; assumption.
  }
  destruct H as [Hlen2 Hlen2'].
  repeat split.
  * auto.
  * constructor; constructor; auto.
  * constructor; constructor; auto.
  * intros * HF [k0 D]. inv D.
    apply ex_intro with (x := k) in H6.
    apply HD1 in H6.
    2: { constructor; auto. constructor; assumption. }
    clear k.
    destruct H6 as [k D].
    eapply term_eval_empty in D as D'; auto.
    2: by apply exp_to_any.
    2: { constructor; auto. constructor; auto. }
    destruct D' as [v [k' [Γ' [HV D']]]].
    eapply frame_indep_core in D' as D''.
    eapply terminates_step_any_2 in D. 2:eassumption.
    simpl in *.
    inv D.
    + specialize (Ho (l ++ Γ)).
      apply match_pattern_length in H2 as H2'.
      rewrite H2' in Ho. clear H2'.
      rewrite length_app in Ho.
      specialize (Ho eq_refl).
      assert (ENVCLOSED (l ++ Γ)) as Hlcl.
      { apply ENVCLOSED_app; auto.
        pose proof (match_pattern_scoped _ _ _ HV H2).
        clear -H.
        induction l.
        * constructor.
        * inv H.
          apply ENVCLOSED_cons; auto.
      }
      specialize (Ho Hlcl).
      destruct Ho as [_ [_ [_ Ho]]].
      apply ex_intro with (x := k0) in H8.
      eapply Ho in H8. 2:auto.
      destruct H8 as [k'' D].
      eapply term_eval_empty in D as D'''; auto.
      2: { apply exp_to_any.
           rewrite length_app.
           apply match_pattern_length in H2. rewrite <- H2.
           auto.
         }
      destruct D''' as [v' [k''' [Γ'' [Hv D''']]]].
      eapply frame_indep_core in D''.
      eapply terminates_step_any_2 in D.
      2: eapply frame_indep_core in D'''; eauto.
      simpl in *.
      eexists. constructor.
      eapply step_term_term_plus.
      eapply frame_indep_core in D'. eauto.
      simpl. eapply term_case_true. eauto.
      eapply step_term_term_plus.
      eapply frame_indep_core in D'''. eauto.
      simpl. eauto.
    + apply ex_intro with (x := k0) in H8.
      apply HD3 in H8. destruct H8 as [i D]. 2:assumption.
      eapply term_eval_empty in D as D'''; auto.
      2: by apply exp_to_any.
      destruct D''' as [v' [k'' [Γ'' [HV' D''']]]].
      eapply frame_indep_core in D''' as D''''.
      eapply terminates_step_any_2 in D. 2:eauto.
      simpl in *.
      eexists. constructor.
      eapply step_term_term_plus.
      eapply frame_indep_core in D'. eassumption.
      simpl. apply term_case_false; auto.
      eapply step_term_term_plus.
      eapply frame_indep_core in D'''. eassumption.
      simpl. exact D.
      Unshelve. auto.
Qed.

Theorem CIU_Case_compat :
  forall Γ e1 e1' e2 e2' e3 e3' p,
    CIU_open Γ e1 e1' ->
    CIU_open (pat_vars p + Γ) e2 e2' ->
    CIU_open Γ e3 e3' ->
    CIU_open Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
  intros * He1 He2 He3 HΓ Hlen Hclosed.
  apply CIU_Case_compat_closed; auto.
  rewrite Hlen. auto.
Qed.

Theorem CIU_BIF_compat_closed :
  forall Γ f1 f2 vals1 vals2,
    CIU Γ f1 f2 ->
    list_biforall (CIU Γ) vals1 vals2 ->
    CIU Γ (EBIF f1 vals1) (EBIF f2 vals2).
Proof.
  intros * [HΓ [Hlf1 [Hlf2 HD]]] Hlbfa.
  apply CIU_list_biforall_scope in Hlbfa as Hl.
  destruct Hl as [Hlv1 Hlv2].
  repeat split.
  * auto.
  * do 2 constructor. auto.
    intros * Hi.
    apply indexed_to_forall with (def := ˝ VLit 0%Z) (i := i) in Hlv1.
    all:auto.
  * do 2 constructor. auto.
    intros * Hi.
    apply indexed_to_forall with (def := ˝ VLit 0%Z) (i := i) in Hlv2.
    all:auto.
  * intros * HF D.
    eapply terminates_step_one in D. 2:constructor.
    eapply step_terminates_one. constructor.
    apply HD in D.
    2: { constructor; auto. constructor; auto. }
    destruct D as [k D].
    eapply term_eval_empty in D as D'; auto.
    2: by apply exp_to_any.
    2: { constructor; auto. constructor; auto. }
    destruct D' as [v [k' [Γ' [HV D']]]].
    eapply frame_indep_core in D' as D''.
    eapply frame_indep_core in D'.
    simpl in D', D''.
    apply ex_intro with (x := k) in D.
    eapply terminates_step_any in D. 2: exact D''. clear D''.
    eapply step_terminates_any. 1: exact D'. clear D'. clear k'.
    clear k. clear Hlf1 Hlf2 HD.
    apply indexed_to_biforall with (d1 := ˝ VLit 0%Z) (d2 := ˝ VLit 0%Z) in Hlbfa.
    destruct Hlbfa as [Hlbfa1 Hlbfa2].
    
    destruct vals1.
    + destruct vals2; try discriminate.
      auto.
    + destruct vals2; try discriminate.
      pose proof (Hlbfa1 0 (Nat.lt_0_succ _)) as Hee0.
      simpl in Hee0.
      eapply terminates_step_one in D. 2:constructor.
      eapply step_terminates_one. constructor.
      apply Forall_cons_1 in Hlv1. destruct Hlv1 as [He Hlv1].
      apply Forall_cons_1 in Hlv2. destruct Hlv2 as [He0 Hlv2].
      destruct Hee0 as [_ [_ [_ HD]]].
      apply HD in D.
      2: { constructor; auto. constructor; auto. }
      clear HD.
      destruct D as [k D].
      eapply term_eval_empty in D as D'; auto.
      2: by apply exp_to_any.
      2: { constructor; auto. constructor; auto. }
      destruct D' as [v' [k' [Γ'' [HV' D']]]].
      eapply frame_indep_core in D' as D''.
      eapply frame_indep_core in D'.
      simpl in D', D''.
      apply ex_intro with (x := k) in D.
      eapply terminates_step_any in D. 2: exact D''. clear D''.
      eapply step_terminates_any. exact D'. clear D'.
      clear k k' Γ'.
      
      remember [] as evd.
      assert (Forall (fun v => VALCLOSED v) evd) as Hevd.
      { subst. auto. }
      clear Heqevd.
      generalize dependent vals2.
      generalize dependent evd.
      generalize dependent v'.
      revert Γ'' v HV.
      induction vals1; intros Γ'' v HV v' HV' evd D Hevd vals2 HD Hl Hlv2.
      - destruct vals2; try discriminate.
        auto.
      - destruct vals2; try discriminate.
        eapply terminates_step_one in D. 2:constructor.
        eapply step_terminates_one. constructor.
        remember HD as HD'. clear HeqHD'.
        specialize (HD' 1).
        assert (1 < length (e :: a :: vals1)) as Hl'. simpl. lia.
        specialize (HD' Hl'). clear Hl'.
        simpl in HD'.
        destruct HD' as [_ [_ [_ HD']]].
        apply HD' in D.
        2: { constructor; auto. constructor; auto.
             apply Forall_app; auto.
             apply Forall_inv_tail in Hlv1; auto. }
        clear HD'.
        destruct D as [k D].
        eapply term_eval_empty in D as D'; auto.
        2: { apply exp_to_any. apply Forall_inv in Hlv2. auto. }
        2: { constructor; auto. constructor; auto.
             apply Forall_app; auto.
             apply Forall_inv_tail in Hlv1. auto. }
        destruct D' as [v'' [k' [Γ' [HV'' D']]]].
        eapply frame_indep_core in D' as D''.
        eapply frame_indep_core in D'.
        simpl in D', D''.
        apply ex_intro with (x := k) in D.
        eapply terminates_step_any in D. 2: exact D''. clear D''.
        eapply step_terminates_any. exact D'. clear D'.
        apply IHvals1; auto.
        ** apply Forall_inv_tail in Hlv1. auto.
        ** apply Forall_app. auto.
        ** intros i Hi.
           destruct i.
           ++ simpl. specialize (HD 0 (Nat.lt_0_succ _)).
              simpl in HD. auto.
           ++ specialize (HD (S (S i))).
              assert (S (S i) < length (e :: a :: vals1)). simpl. simpl in Hi. lia.
              specialize (HD H). simpl in HD.
              simpl. auto.
        ** apply Forall_inv_tail in Hlv2. auto.
Qed.

Theorem CIU_BIF_compat :
  forall Γ f1 f2 vals1 vals2,
    CIU_open Γ f1 f2 ->
    list_biforall (CIU_open Γ) vals1 vals2 ->
    CIU_open Γ (EBIF f1 vals1) (EBIF f2 vals2).
Proof.
  intros * Ho Hlbfa Γ0 Hlen HΓ0.
  apply CIU_BIF_compat_closed; auto.
  eapply indexed_to_biforall with (d1 := ˝VLit 0%Z) (d2 := ˝VLit 0%Z) in Hlbfa.
  eapply indexed_to_biforall with (d1 := ˝VLit 0%Z) (d2 := ˝VLit 0%Z).
  destruct Hlbfa.
  split; auto.
  intros i Hl.
  specialize (H i Hl).
  unfold CIU_open in H.
  specialize (H Γ0 Hlen HΓ0). auto.
Qed.
