(**
  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we show example program equivalences in sequential Core Erlang.
*)
Require Import CTX.
Import ListNotations.

Lemma Equiv_refl :
  forall e Γ, EXP Γ ⊢ e -> e ≈[Γ]≈ e. Proof. intros. split; now apply CTX_refl. Qed.

Lemma Equiv_sym :
  forall e1 e2 Γ, e1 ≈[Γ]≈ e2 -> e2 ≈[Γ]≈ e1.
Proof.
  intros. destruct H; auto.
Qed.

Lemma Equiv_trans :
  forall e1 e2 e3 Γ, e1 ≈[Γ]≈ e2 -> e2 ≈[Γ]≈ e3
->
  e1 ≈[Γ]≈ e3.
Proof.
  intros. assert (Transitive (CTX Γ)). { apply CTX_IsPreCtxRel. }
  destruct H, H0. split.
  * eapply H1; eauto.
  * eapply H1; eauto.
Qed.

Corollary let_abs : forall e2 v x,
  EXP 1 ⊢ e2 -> VALCLOSED v ->
  e2.[v/] ≈ ELet x v e2.
Proof.
  intros. split; now apply CIU_iff_CTX, CIU_beta_value.
Qed.

Corollary let_abs_core : forall Γ e2 v x,
  EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
  e2.[v/] ≈[Γ]≈ ELet x v e2.
Proof.
  intros. split; now apply CIU_iff_CTX, CIU_beta_value.
Qed.

Corollary beta_abs : forall {Γ e vl vals},
  VAL Γ ⊢ EFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals ->
  e.[list_subst (EFun vl e :: vals) idsubst] ≈[Γ]≈ EApp (EFun vl e) vals.
Proof.
  intros. split; now eapply CTX_beta_values.
Qed.

Ltac cpb_term :=
match goal with
| [ H : | _, EApp _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, EBIF _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, ELet _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, ELetRec _ _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, ECase _ _ _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _ :: _, _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
end.

Ltac term_step :=
match goal with
| [ H : | ?Fs, ?e | _ ↓, H1 : ⟨ ?Fs, ?e ⟩ -[_]-> ⟨_, _⟩ |- _ ] =>
  eapply (terminates_step_any_2 _ _ _ _ H) in H1 as ?P
end.

Theorem plus_comm : forall Γ e1 e2,
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2 ->
  EBIF (ELit "+"%string) [e1; e2] ≈[Γ]≈ EBIF (ELit "+"%string) [e2; e1].
Proof.
  assert (forall e1 e2, EXPCLOSED e1 -> EXPCLOSED e2 -> CIU (EBIF (ELit "+"%string) [e1; e2]) (EBIF (ELit "+"%string) [e2; e1])). {
    split. 2: split. 1-2: constructor; eauto.
    1-2: intros; destruct i; simpl in *; [auto | destruct i; [auto | lia ] ].
    intros. destruct H2.
    do 2 cpb_term.
    apply term_eval_both in H9 as Eval1; auto.
    destruct Eval1 as [v1 [k1 [v_v1 [Eval1_1 Eval1_2]]]]. term_step.
    cpb_term.
    apply term_eval_both in H13 as Eval1; auto.
    destruct Eval1 as [v2 [k2 [v_v2 [Eval2_1 Eval2_2]]]].
    term_step.
    cpb_term.
    exists (3 + k1 + k2 + S k3). simpl.
    constructor. constructor. auto.

    eapply term_step_term.
    eapply frame_indep_nil in Eval2_1. exact Eval2_1.
    replace (S (k1 + k2 + S k3) - k2) with (S (k1 + S k3)) by lia.

    constructor; auto. 2: lia.
    eapply term_step_term.
    eapply frame_indep_nil in Eval1_1. exact Eval1_1.
    replace (k1 + S k3 - k1) with (S k3) by lia.

    constructor.
    now rewrite Z.add_comm. lia.
  }
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; apply H.
  all: apply -> subst_preserves_scope_exp; eauto.
Qed.

Corollary eval_equiv :
  forall e1 v : Exp, EXPCLOSED e1 -> ⟨ [], e1 ⟩ -->* v
->
  e1 ≈ v.
Proof.
  apply CTX_eval.
Qed.

Theorem let_delay : forall Γ e x e',
  EXP Γ ⊢ e -> EXPCLOSED e' -> | [], e' | ↓ ->
  e ≈[Γ]≈ ELet x e' (rename (fun n => S n) e).
Proof.
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; split;
    [idtac|split|idtac|split]. 2, 4: constructor.
  3, 5: rewrite renaming_is_subst.
  1, 3-4, 7: apply -> subst_preserves_scope_exp; eauto.
  1-4: apply -> subst_preserves_scope_exp; eauto.
  1-2: intro; intros; simpl; lia.
  1-2: intro; intros; inversion H3.
  * intros. destruct H4, H1.
    apply term_eval in H1. destruct H1, H1, H1.
    eapply frame_indep_nil in H5. assert (e'.[ξ] = e'). 
    { rewrite eclosed_ignores_sub; auto. } rewrite H6 in *.
    exists (S (x3 + S x0)). constructor.
    eapply term_step_term. simpl in H5. exact H5.
    replace (x3 + S x0 - x3) with (S x0) by lia.
    
    constructor; auto. 2: lia.
    rewrite renaming_is_subst, subst_comp, subst_extend, subst_comp.
    replace (ren (fun n : nat => S n) >> inl x2 .:: ξ) with (ξ) by reflexivity. auto. auto.
  * intros. destruct H4. cpb_term.
    apply term_eval_both in H10 as H10'. destruct H10' as [v [k0 [v_v [Eval1 Eval2]]]].
    term_step.
    cpb_term. exists k1.
    rewrite renaming_is_subst, subst_comp, subst_extend, subst_comp in H11.
    exact H11. now rewrite eclosed_ignores_sub.
Qed.

Theorem eta_abstraction Γ e :
  EXP Γ ⊢ e ->
  e ≈[Γ]≈ EApp (EFun [] (rename (fun n => S n) e)) [].
Proof.
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; split;
  [idtac|split|idtac|split].
  2, 4: constructor. 2, 4: do 2 constructor.
  all: try apply -> subst_preserves_scope_exp; eauto.
  3-4: intros; inversion H1.
  1-2: rewrite renaming_is_subst; apply -> subst_preserves_scope_exp; eauto.
  1-2: intro; intros; simpl; lia.
  * intros. destruct H2 as [x H2]. exists (S (S x)).
    constructor. constructor.
    rewrite renaming_is_subst, subst_comp, subst_comp, subst_extend, subst_comp.
    now replace (ren (fun n : nat => S n) >> EFun [] e.[ren (fun n : nat => S n) >> up_subst ξ] .: ξ) with ξ by reflexivity.
  * intros. destruct H2 as [x H2].
    inversion H2; subst; try inversion_is_value.
    inversion H7; subst.
    rewrite renaming_is_subst, subst_comp, subst_comp, subst_extend, subst_comp in H5.
    replace (ren (fun n : nat => S n) >> EFun [] e.[ren (fun n : nat => S n) >> up_subst ξ] .: ξ) with ξ in H5 by reflexivity. now exists k0.
Qed.

Theorem general_eta_abstraction Γ e vl vals :
  length vl = length vals -> EXP Γ ⊢ e -> Forall (fun v => VALCLOSED v) vals ->
  e ≈[Γ]≈ EApp (EFun vl (rename (fun n => S (length vl) + n) e)) vals.
Proof.
  intros. split; eapply CIU_iff_CTX; intro; intros; simpl; split;
  [idtac|split|idtac|split].
  2, 4: constructor. 2, 4: do 2 constructor.
  1,7: try apply -> subst_preserves_scope_exp; eauto.
  1-2: rewrite renaming_is_subst, subst_comp; apply -> subst_preserves_scope_exp; eauto.
  1-2: apply substcomp_scoped with (Δ := S (length vl) + Γ).
  2, 4 : now apply up_scope, upn_scope.
  1-2: intro; intros; cbn; lia.
  1-2: intros; rewrite Forall_nth in H1; apply scoped_val.
  1-2: now replace (ELit 0%Z) with ((ELit 0%Z).[ξ]) by auto; rewrite map_nth;
    rewrite map_length in H3;
    apply vclosed_sub_closed, H1.
  * intros. destruct H4 as [k H4].
    eexists. apply term_app_in_k.
    - shelve.
    - now rewrite map_length.
    - eapply Forall_map; auto. eapply Forall_impl. 2: exact H1. intros.    now apply vclosed_sub_closed.
    - repeat rewrite renaming_is_subst, subst_comp, subst_comp in *.
      fold_upn. fold_list_subst.
      replace (fun n => S (length vl + n)) with (fun n => S (length vl) + n) by auto.
      rewrite rename_upn_list_subst. exact H4.
      simpl. rewrite map_length. auto.
  * intros. destruct H4 as [k H4].
    epose proof (full_eval_app_partial (rename (fun n : nat => S (Datatypes.length vl + n)) e).[
          up_subst (upn (Datatypes.length vl) ξ)] (map (subst ξ) vals) vl F _ _).
    repeat rewrite renaming_is_subst, subst_comp, subst_comp in H5.
    fold_upn_hyp. fold_list_subst_hyp.
    replace (fun n => S (length vl + n)) with (fun n => S (length vl) + n) in H5 by auto.
    rewrite substcomp_assoc in H5.
    rewrite rename_upn_list_subst in H5.
    eexists. eapply terminates_step_any_2. exact H4.
    rewrite renaming_is_subst, subst_comp. simpl in H5. apply H5.
    simpl. rewrite indexed_to_forall in H1. rewrite indexed_to_forall.
    intros. rewrite map_nth, vclosed_ignores_sub. apply H1. rewrite map_length in H6. auto.
    apply H1. rewrite map_length in H6. auto.
    simpl. rewrite map_length. lia.
  Unshelve.
    3: rewrite map_length; lia.
    3: exact (ELit 0%Z).
    all: simpl; constructor; rewrite renaming_is_subst, subst_comp, Nat.add_0_r.
    all: apply -> subst_preserves_scope_exp; [ exact H0 | ]; apply substcomp_scoped with (Δ := Γ + S (length vl)).
    + intro. intros. simpl. lia.
    + rewrite Nat.add_comm. simpl. apply up_scope. rewrite <- (Nat.add_0_r (length vl)) at 2.
      apply upn_scope. auto.
    + intro. intros. simpl. lia.
    + rewrite Nat.add_comm. simpl. apply up_scope. rewrite <- (Nat.add_0_r (length vl)) at 2.
      apply upn_scope. auto.
Qed.

Definition naive_equivalent (e1 e2 : Exp) : Prop :=
  forall v F, FSCLOSED F /\ EXPCLOSED e1 /\ EXPCLOSED e2 /\ 
    (⟨ F, e1 ⟩ -->* v -> ⟨ F, e2 ⟩ -->* v).

Theorem naive_equivalent_implies_ciu :
  forall e1 e2,
  naive_equivalent e1 e2 -> CIU e1 e2.
Proof.
  unfold naive_equivalent, CIU; intros.
  split; [|split].
  1-2: apply H. 1,3: exact (ELit 0%Z). 1-2: exact [].
  intros. apply terminates_eq_terminates_sem in H1 as [v H1].
  apply H in H1. now apply ex_intro, terminates_eq_terminates_sem in H1.
Qed.


(* Definition unfold_app (l : list Var) (l2 : list Exp) (b : Exp) : Exp :=
  fold_right (fun '(x, e) Acc => ELet x e (rename (fun n => S n) Acc)) b (combine l l2). *)

Fixpoint n_vars (n : nat) : list Exp :=
match n with
| 0 => []
| S n' => EVar n' :: n_vars n'
end.

Fixpoint unfold_app (l : list Var) (l2 : list Exp) (body : Exp) : option Exp :=
match l, l2 with
| [], [] => Some body
| x::xs, e::es => 
         match (unfold_app xs (map (rename (fun n => S n)) es) body) with
         | None => None
         | Some e' => Some (ELet x e e')
         end
| _, _ => None
end.

Theorem unfold_app_length : forall xs es b,
  length xs = length es ->
  unfold_app xs es b = None -> False.
Proof.
  induction xs; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. inversion H0.
  * apply element_exist in H as H'. destruct H', H1. subst. inversion H.
    simpl in H0. break_match_hyp. inversion H0.
    eapply IHxs. 2: exact Heqo. rewrite map_length. auto.
Qed.

Theorem CIU_evaluates :
  forall e1 e2 v, EXPCLOSED e1 -> EXPCLOSED e2 ->
  ⟨[], e1⟩ -->* v -> ⟨[], e2⟩ -->* v ->
  CIU e1 e2.
Proof.
  intros.
  split. 2: split. 1-2: auto.
  intros.
  destruct H1 as [CL1 [k1 H1]], H2 as [CL2 [k2 H2]].
  apply frame_indep_nil with (Fs' := F) in H2. simpl in H2.
  apply frame_indep_nil with (Fs' := F) in H1. simpl in H1.
  destruct H4 as [k1' H4].
  eapply terminates_step_any_2 in H1. 2: exact H4.
  eapply term_step_term_plus in H2. 2: exact H1.
  now exists (k2 + (k1' - k1)).
Qed.

Theorem map_foldr_equiv :
  forall l' l x y z e f
  (VsCL : VALCLOSED l) (SCE : EXP 2 ⊢ e),
  computes x e f -> cons_to_list l = Some l' ->
  CIU (obj_map (EFun [x] e) l) (obj_foldr (EFun [y;z] (ECons (EApp (EFun [x] e) [EVar 1]) (EVar 2))) l ENil).
Proof.
  intros.
  pose proof (obj_foldr_on_meta_level l' l x y z e f VsCL SCE H H0).
  pose proof (obj_map_on_meta_level l' l x e f VsCL SCE H H0).
  eapply CIU_evaluates; eauto.
  {
    unfold obj_map. do 3 constructor; auto; simpl.
    - constructor. simpl. constructor; auto.
      cbn. constructor; auto.
      destruct i. 2: destruct i.
      all: constructor. lia.
    - do 2 constructor; auto. simpl in H3.
      destruct i. 2: destruct i. 3: destruct i. all: constructor. all: lia.
    - simpl in *. destruct i. 2: destruct i.
      constructor; simpl. now apply (proj2 (scope_ext_app 3 2 ltac:(lia))).
      now apply (proj1 (scope_ext_app 1 0 ltac:(lia))).
      lia.
  }
  {
    unfold obj_map. do 3 constructor; auto; simpl.
    - do 2 constructor; auto.
    - intros. destruct i. 2: destruct i. 3: destruct i.
      constructor. constructor. lia.
      all: auto.
      constructor. do 2 constructor. lia. simpl.
      intros. destruct i. 2: destruct i. 3: destruct i.
      1-3: do 2 constructor. all: lia.
    - do 2 constructor; auto.
    - simpl in *. destruct i. 2: destruct i. 3: destruct i.
      do 3 constructor; simpl. all: auto.
      + do 2 constructor. simpl. now apply (proj2 (scope_ext_app 6 2 ltac:(lia))).
      + intros. destruct i. do 2 constructor. all: lia.
      + now apply (proj1 (scope_ext_app 1 0 ltac:(lia))).
      + lia.
  }
Qed.

Theorem map_foldr_equiv_rev :
  forall l' l x y z e f
  (VsCL : VALCLOSED l) (SCE : EXP 2 ⊢ e),
  computes x e f -> cons_to_list l = Some l' ->
  CIU (obj_foldr (EFun [y;z] (ECons (EApp (EFun [x] e) [EVar 1]) (EVar 2))) l ENil) (obj_map (EFun [x] e) l).
Proof.
  intros.
  pose proof (obj_foldr_on_meta_level l' l x y z e f VsCL SCE H H0).
  pose proof (obj_map_on_meta_level l' l x e f VsCL SCE H H0).
  eapply CIU_evaluates; eauto.
  2: {
    unfold obj_map. do 3 constructor; auto; simpl.
    - constructor. simpl. constructor; auto.
      cbn. constructor; auto.
      destruct i. 2: destruct i.
      all: constructor. lia.
    - do 2 constructor; auto. simpl in H3.
      destruct i. 2: destruct i. 3: destruct i. all: constructor. all: lia.
    - simpl in *. destruct i. 2: destruct i.
      constructor; simpl. now apply (proj2 (scope_ext_app 3 2 ltac:(lia))).
      now apply (proj1 (scope_ext_app 1 0 ltac:(lia))).
      lia.
  }
  {
    unfold obj_map. do 3 constructor; auto; simpl.
    - do 2 constructor; auto.
    - intros. destruct i. 2: destruct i. 3: destruct i.
      constructor. constructor. lia.
      all: auto.
      constructor. do 2 constructor. lia. simpl.
      intros. destruct i. 2: destruct i. 3: destruct i.
      1-3: do 2 constructor. all: lia.
    - do 2 constructor; auto.
    - simpl in *. destruct i. 2: destruct i. 3: destruct i.
      do 3 constructor; simpl. all: auto.
      + do 2 constructor. simpl. now apply (proj2 (scope_ext_app 6 2 ltac:(lia))).
      + intros. destruct i. do 2 constructor. all: lia.
      + now apply (proj1 (scope_ext_app 1 0 ltac:(lia))).
      + lia.
  }
Qed.

