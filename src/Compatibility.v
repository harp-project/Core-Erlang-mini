Require Import LogRel.
Import ListNotations.

Lemma Vrel_Var_compat :
  forall Γ x,
  In (inl x) Γ ->
  Vrel_open Γ (EVar x) (EVar x).
Proof.
  unfold Vrel_open, Grel.
  cbn. intuition.
Qed.

Hint Resolve Vrel_Var_compat.

Lemma Vrel_FunId_compat :
  forall Γ x,
  In (inr x) Γ ->
  Vrel_open Γ (EFunId x) (EFunId x).
Proof.
  unfold Vrel_open, Grel.
  cbn. intuition.
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

Definition composition {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).

Lemma compose_subst :
  forall ξ₁ ξ₂ e, subst ξ₁ (subst ξ₂ e) = composition (subst ξ₁) (subst ξ₂) e.
Proof.
  intros. unfold composition. reflexivity.
Qed.

Lemma subst_list_not_in :
  forall l x, ~In x l ->
  forall ξ vs, length l = length vs -> (ξ[[::= combine l vs]]) x = ξ x.
Proof.
  induction l; intros.
  * simpl. auto.
  * apply element_exist in H0 as H0'. destruct H0', H1. subst. inversion H0. simpl.
    apply not_in_cons in H. destruct H.
    replace (ξ x) with (ξ [[a ::= x0]] x). apply IHl; auto.
    apply not_eq_sym, var_funid_eqb_neq in H. unfold extend_subst. rewrite H. auto. 
Qed.

Lemma subst_list_in :
  forall l x, In x l ->
  forall ξ φ vs, length l = length vs -> (ξ[[ ::= combine l vs]]) x = (φ[[::= combine l vs]]) x.
Proof.
  induction l; intros.
  * inversion H.
  * apply element_exist in H0 as H0'. destruct H0', H1. subst. inversion H0. simpl.
    unfold extend_subst. destruct (in_dec var_funid_eq_dec x l).
    - apply IHl; auto.
    - inversion H. 2: contradiction. subst. repeat rewrite subst_list_not_in; auto.
      rewrite var_funid_eqb_refl. auto.
Qed.

Lemma subst_composition :
  forall e ξ l vals Γ, length l = length vals -> subscoped Γ [] ξ ->
  composition (subst (idsubst[[ ::= combine l vals]])) (subst (ξ -- l)) e = subst (ξ[[::= combine l vals]]) e.
Proof.
  induction e; intros; unfold composition; simpl; auto.
  * unfold "--". simpl. destruct (in_list (inl v) l) eqn:P.
    - simpl. apply subst_list_in; auto. apply in_list_sound in P. auto. 
    - apply not_in_list_sound in P. rewrite subst_list_not_in; auto. unfold subscoped in H0.
      rewrite subst_list_not_in.
Qed.

Lemma Vrel_Fun_compat :
  forall Γ vl b1 b2,
  Erel_open (Γ ++ map inl vl) b1 b2 ->
  Vrel_open Γ (EFun vl b1) (EFun vl b2).
Proof.
  intros. unfold Vrel_open. intros.
  inversion H0 as [? [? ?] ].
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor. eapply subst_preserves_scope_rev; eauto. eapply Erel_open_scope in H. apply H.
  - constructor. eapply subst_preserves_scope_rev; eauto. eapply Erel_open_scope in H. apply H.
  - break_match_goal; try congruence. intros. unfold Erel_open in H.
    unfold Erel in H.
     eapply H.
Qed.

