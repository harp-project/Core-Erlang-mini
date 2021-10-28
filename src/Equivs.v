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
| [ H : | _, EPlus _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
| [ H : | _, EApp _ _ | _ ↓ |- _ ] => inversion H; subst; try inversion_is_value; clear H
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
  EPlus e1 e2 ≈[Γ]≈ EPlus e2 e1.
Proof.
  assert (forall e1 e2, EXPCLOSED e1 -> EXPCLOSED e2 -> CIU (EPlus e1 e2) (EPlus e2 e1)). {
    split. 2: split. 1-2: constructor; eauto.
    intros. destruct H2. cpb_term.
    apply term_eval_both in H7 as Eval1.
    destruct Eval1 as [v1 [k1 [v_v1 [Eval1_1 Eval1_2]]]]. term_step.
    cpb_term.
    apply term_eval_both in H8 as Eval1. destruct Eval1 as [v2 [k2 [v_v2 [Eval2_1 Eval2_2]]]].
    term_step.
    cpb_term.
    exists (3 + (k2 + (k1 + k3))). constructor.
    
    eapply term_step_term.
    eapply frame_indep_nil in Eval2_1. exact Eval2_1.
    replace (S (S (k2 + (k1 + k3))) - k2) with (S (S (k1 + k3))) by lia.
    
    constructor; auto. 2: lia.
    eapply term_step_term.
    eapply frame_indep_nil in Eval1_1. exact Eval1_1.
    replace (S (k1 + k3) - k1) with (S k3) by lia.
    
    constructor.
    now rewrite Z.add_comm. lia.
    all: auto.
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
  Search up_subst ">>".
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
  1-2: now replace (ELit 0) with ((ELit 0).[ξ]) by auto; rewrite map_nth;
    rewrite map_length in H3;
    apply vclosed_sub_closed, H1.
  * intros. destruct H4 as [k H4].
    eexists. apply term_app_in_k.
    - shelve.
    - now rewrite map_length.
    - eapply Forall_map; auto.
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
    3: exact (ELit 0).
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
  1-2: apply H. 1,3: exact (ELit 0). 1-2: exact [].
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

Compute unfold_app ["X"%string; "Y"%string] [ELit 0; EVar 0] (EApp (EVar 0) [EVar 1]).

Theorem let_many : forall xs vals b Γ e,
  length xs = length vals -> unfold_app xs vals b = Some e -> 
  EXP Γ ⊢ b -> Forall (fun v => VAL Γ ⊢ v) vals
->
  b.[list_subst vals idsubst] ≈[Γ]≈ e.
Proof.
  induction xs; intros; cbn.
  * apply eq_sym, length_zero_iff_nil in H. subst. cbn. rewrite idsubst_is_id.
    inversion H0. subst. now apply Equiv_refl.
  * apply element_exist in H as H'. destruct H', H3. subst.
    simpl in H0. break_match_hyp. 2: congruence. inversion H0. inversion H. inversion H2. subst.
    eapply IHxs in Heqo. 3: exact H1. 2: now rewrite map_length. inversion H0.
    subst. simpl.
    epose proof (let_abs_core).
    eapply Equiv_trans. 2: apply H2.


Theorem app_fix_eval_order : forall xs Γ x e vals b vl,
  (* NoDup (x::xs) -> *) length xs = length vals -> length vl = length vals ->
  VAL Γ ⊢ (EFun vl b) -> Forall (fun e => VAL Γ ⊢ e) vals ->
  unfold_app (x::xs) ((EFun vl b)::vals) (EApp (EVar (length xs)) (n_vars (length xs))) = Some e
->
  EApp (EFun vl b) vals ≈[Γ]≈ e.
Proof.
  intros. simpl in H3. break_match_hyp. 2: congruence.
  inversion H3. subst. clear H3.
  
  epose proof (ETA := eta_abs H1 H2 H0). apply Equiv_sym in ETA.
  eapply Equiv_trans. exact ETA. clear ETA.
  epose proof (LET := let_abs_core _ _ _ _ _ _). apply Equiv_sym in LET.
  apply Equiv_sym. eapply Equiv_trans. exact LET. clear LET. simpl.
  
  
  
  
  
  
  
  
  induction xs; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst.
    apply length_zero_iff_nil in H0. subst. cbn.
    epose proof (let_abs_core Γ (EApp (EVar 0) []) (EFun [] b) x _ H1).
    simpl in H3. inversion H3. subst. exact H.
  * simpl in H3. break_match_hyp. break_match_hyp; subst. all: try congruence.
    inversion H3. break_match_hyp. 2: congruence. inversion Heqo. subst.
    
    epose proof (ETA := eta_abs H1 H2 H0).
    apply element_exist in H as H'. destruct H', H4. subst. inversion H.
    apply eq_sym, element_exist in H0 as H'. destruct H', H4. subst. inversion H0. 
    eapply Equiv_trans. apply Equiv_sym in ETA. exact ETA.
    
    epose proof (let_abs_core _ _ _ _ _ _). apply Equiv_sym in H4.
    apply Equiv_sym. eapply Equiv_trans. exact H4. simpl.
  
    epose proof (IHxs Γ a).
  
  
  
  
  generalize dependent exps. generalize dependent vl.
  generalize dependent b. generalize dependent e. generalize dependent xs.
  induction xs; intros; cbn.
  { apply eq_sym, length_zero_iff_nil in H. subst.
    apply length_zero_iff_nil in H0. subst. cbn.
    epose proof (let_abs_core Γ (EApp (EVar 0) []) (EFun [] b) x _ H1).
    simpl in Heqo. inversion Heqo. subst. exact H.
  }
  {
    apply element_exist in H as H'. destruct H', H3. subst. inversion H.
    apply eq_sym, element_exist in H0 as H'. destruct H', H3. subst. inversion H0.
    simpl in Heqo. break_match_hyp. break_match_hyp. 2-3: congruence.
    inversion Heqo. inversion Heqo0. subst. inversion H2. subst.
    epose proof (IHxs _ _ _ _ _ H4 (eq_sym H5) H8 _).
    Unshelve.
    all: auto.
  }
  
  (* intros. split; eapply CIU_iff_CTX; intro; intros; simpl; split;
    [idtac|split|idtac|split].
   *)

Qed.


