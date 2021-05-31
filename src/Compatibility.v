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

(* Lemma subst_composition :
  forall e ξ l vals Γ, length l = length vals -> subscoped Γ [] ξ ->
  EXP Γ ++ l ⊢ e ->
  composition (subst (idsubst[[ ::= combine l vals]])) (subst (ξ -- l)) e = subst (ξ[[::= combine l vals]]) e.
Proof.
  induction e; intros; unfold composition; simpl; auto.
  * unfold "--". simpl. destruct (in_list (inl v) l) eqn:P.
    - simpl. apply subst_list_in; auto. apply in_list_sound in P. auto. 
    - inversion H1. inversion H2. subst. apply not_in_list_sound in P.
      apply in_app_iff in H5. destruct H5. 2: contradiction.
      rewrite subst_list_not_in; auto.
      specialize (H0 _ H3). eapply vclosed_ignores_sub in H0. rewrite H0. reflexivity.
  * unfold "--". simpl. destruct (in_list (inr f) l) eqn:P.
    - simpl. apply subst_list_in; auto. apply in_list_sound in P. auto. 
    - inversion H1. inversion H2. subst. apply not_in_list_sound in P.
      apply in_app_iff in H5. destruct H5. 2: contradiction.
      rewrite subst_list_not_in; auto.
      specialize (H0 _ H3). eapply vclosed_ignores_sub in H0. rewrite H0. reflexivity.
  * assert ((subst ((idsubst [[ ::= combine l vals]]) -- map inl vl) (subst ((ξ -- l) -- map inl vl) e)) = (subst ((ξ [[ ::= combine l vals]]) -- map inl vl) e)).
    { unfold composition in IHe.
Abort. *)

Definition varname (e : Exp) : option VarFunId :=
match e with
| EVar v   => Some (inl v)
| EFunId f => Some (inr f)
| _        => None
end.

Definition substcomp (ξ η : Substitution) : Substitution :=
  composition (subst ξ) η.
(* fun x =>
  match (varname (η x)) with
  | Some vname => ξ vname
    (* if var_funid_eqb vname x
    then ξ x
    else η x *)
  | _ => η x
end. *)
(* 
Lemma idsubst_varname : forall x, varname (idsubst x) = Some x.
Proof.
  intros. destruct x; cbn; auto.
Qed.
*)

Lemma subst_restrict_app :
  forall ξ l1 l2, ((ξ -- l1) -- l2) = (ξ -- (l1 ++ l2)).
Proof.
  intros. extensionality x. unfold "--". break_match_goal.
  * apply in_list_sound in Heqb. eapply in_app_right in Heqb.
    apply in_list_sound in Heqb. rewrite Heqb. auto.
  * break_match_goal.
    - apply in_list_sound in Heqb0. eapply in_app_left in Heqb0.
      apply in_list_sound in Heqb0. rewrite Heqb0. auto.
    - apply not_in_list_sound in Heqb. apply not_in_list_sound in Heqb0.
      eapply app_not_in in Heqb; eauto. apply not_in_list_sound in Heqb. rewrite Heqb. auto.
Qed.

(* Lemma subst_composition :
  forall e ξ η l,
  (subst (η[[::= l]])) (subst (ξ -- fst (split l)) e) = 
  subst (substcomp (η[[::= l]]) (ξ -- fst (split l))) e.
Proof.
  induction e; intros; auto; simpl.
  * Search "--". rewrite subst_restrict_app.
Abort. *)

(** In general, the following lemma could not be weakened more:
    (ξ₁ -- l) cannot be replaced by ξ₁ on the right-hand side.
*)
Lemma substcomp_restrict : forall ξ₁ ξ₂ l,
  (substcomp (ξ₁ -- l) (ξ₂ -- l)) = (substcomp (ξ₁ -- l) ξ₂ -- l).
Proof.
  intros. unfold "--". extensionality x.
  break_match_goal; cbn.
  * rewrite Heqb. destruct x; simpl; break_match_goal; auto.
    - apply in_list_sound in Heqb. apply not_in_list_sound in Heqb0. contradiction. (* Coq bug *)
    - apply in_list_sound in Heqb. apply not_in_list_sound in Heqb0. contradiction.
  * rewrite Heqb. unfold substcomp, composition. reflexivity.
Qed.

(*
    What if ξ₂ produced closed values? Or just ξ₂'s result is NOT containing any
    variables of l?
*)
Lemma substcomp_restrict_x : forall ξ₁ ξ₂ l x, VALCLOSED (ξ₂ x) ->
  (substcomp (ξ₁ -- l) (ξ₂ -- l)) x = (substcomp ξ₁ ξ₂ -- l) x.
Proof.
  intros. rewrite substcomp_restrict. unfold substcomp, "--", composition.
  break_match_goal; auto.
  eapply vclosed_ignores_sub in H as H'. rewrite H'.
  eapply vclosed_ignores_sub in H. rewrite H. auto.
Qed.

(* Lemma subscoped_app_restrict : forall Γ ξ Γ' l,
  subscoped Γ Γ' ξ -> subscoped (Γ ++ l) Γ' (ξ -- l).
Proof.
  intros. unfold subscoped in *. intros. unfold "--". break_match_goal.
Abort. *)
(* 
Fixpoint bound_variables (e : Exp) : list VarFunId :=
match e with
 | ELit l => []
 | EVar v => []
 | EFunId f => []
 | EFun vl e => map inl vl ++ bound_variables e
 | ERecFun f vl e => inr f :: map inl vl ++ bound_variables e
 | EApp exp l => bound_variables exp ++ fold_left (fun acc e => bound_variables e ++ acc) l []
 | ELet v e1 e2 => inl v :: bound_variables e1 ++ bound_variables e2
 | ELetRec f vl b e => inr f :: map inl vl ++ bound_variables b ++ bound_variables e
 | EPlus e1 e2 => bound_variables e1 ++ bound_variables e2
 | EIf e1 e2 e3 => bound_variables e1 ++ bound_variables e2 ++ bound_variables e3
end.

Fixpoint free_variables (e : Exp) : list VarFunId :=
match e with
 | ELit l => []
 | EVar v => [inl v]
 | EFunId f => [inr f]
 | EFun vl e => filter (fun name => negb (in_list name (map inl vl))) (free_variables e)
 | ERecFun f vl e => filter (fun name => negb (in_list name (inr f :: map inl vl))) (free_variables e)
 | EApp exp l => free_variables exp ++ fold_left (fun acc e => free_variables e ++ acc) l []
 | ELet v e1 e2 => free_variables e1 ++ filter (fun name => negb (var_funid_eqb name (inl v))) (free_variables e2)
 | ELetRec f vl b e => filter (fun name => negb (in_list name (inr f :: map inl vl))) (free_variables b) ++ filter (fun name => negb (var_funid_eqb name (inr f))) (free_variables e)
 | EPlus e1 e2 => free_variables e1 ++ free_variables e2
 | EIf e1 e2 e3 => free_variables e1 ++ free_variables e2 ++ free_variables e3
end.

Compute free_variables (sum 114).

Local Definition l1 := ELet "X"%string (EVar "X"%string) (EVar "X"%string).
Compute bound_variables l1.

Definition capture_avoiding_subst (l : list VarFunId) (ξ : Substitution) :=
  forall x, filter (fun name => in_list name l) (free_variables (ξ x)) = []. *)

Corollary substcomp_restrict_subscoped : forall e ξ₁ ξ₂ l Γ, subscoped Γ [] ξ₂ ->
  EXP Γ ⊢ e ->
  subst (substcomp (ξ₁ -- l) (ξ₂ -- l)) e = subst (substcomp ξ₁ ξ₂ -- l) e.
Proof.
  induction e; intros; simpl; auto.
  * apply substcomp_restrict_x. apply H. inversion H0. inversion H1. auto.
  * apply substcomp_restrict_x. apply H. inversion H0. inversion H1. auto.
  * inversion H0. inversion H1. subst.
    rewrite subst_restrict_comm. erewrite <- IHe.
    rewrite subst_restrict_comm. replace ((ξ₂ -- l) -- map inl vl) with ((ξ₂ -- map inl vl) -- l). 2: apply subst_restrict_comm. repeat rewrite subst_restrict_app. erewrite IHe.
    auto.
  
(* (*     rewrite subst_restrict_comm, substcomp_restrict, subst_restrict_comm. erewrite IHe. 3: eauto.
    subst_restrict_comm. auto. *) *)
Abort.

(**
  with capture-avoiding substitution, this should be trivial

  However, if we substitute bound variables to closed values, it should not be a problem.
*)
Lemma subst_composition2 :
  forall e ξ₁ ξ₂ Γ, EXP Γ ⊢ e -> subscoped Γ [] ξ₂ ->
  (subst ξ₁) (subst ξ₂ e) = subst (substcomp ξ₁ ξ₂) e.
Proof.
  induction e; intros; simpl; auto.
  * erewrite IHe.
Admitted.

(* Lemma subst_composition_scoped :
  forall ξ η Γ Γ', subscoped Γ Γ' ξ -> subscoped Γ Γ' η -> subscoped Γ Γ' (substcomp ξ η).
Proof.
(*   intros. intro. intros. unfold substcomp. break_match_goal;
  [ apply H | apply H0 ]; auto. *)
  
Abort. *)

Lemma subst_list_in_val : forall l x vals ξ, length l = length vals ->
  In x l -> exists v, In v vals /\ (ξ[[ ::= combine l vals]]) x = v.
Proof.
  induction l; intros.
  * inversion H0.
  * apply element_exist in H as H0'. destruct H0', H1. subst. inversion H.
    unfold extend_subst. destruct (in_dec var_funid_eq_dec x l).
    - epose (IHl x x1 _ H2 i). destruct e, H1. exists x2. split. firstorder.
      simpl. eexact H3.
    - inversion H0. 2: contradiction. subst.
      exists x0. split. firstorder. simpl.
      repeat rewrite subst_list_not_in; auto.
      unfold extend_subst. rewrite var_funid_eqb_refl. auto.
Qed.

(* Lemma subscoped_ext_app :
  forall ξ Γ Γ' l vals, subscoped Γ Γ' ξ -> length l = length vals ->
  Forall (fun v => VAL Γ' ⊢ v ) vals ->
  subscoped (Γ ++ l) Γ' (substcomp (idsubst[[::= combine l vals]]) (ξ -- l)).
Proof.
  intros. intro. intros. unfold "--", substcomp. (* break_match_goal.
  * break_match_hyp.
    - apply in_list_sound in Heqb. Check subst_list_in.
      epose (subst_list_in_val _ _ _ _ H0 Heqb). destruct e. destruct H3.
      rewrite H4. rewrite indexed_to_forall in H1. (* Just technical, but doable *) *)
Admitted. *)

Lemma biforall_vrel_helper : forall m vals1 vals2, length vals1 = length vals2 ->
  list_biforall (Vrel m) vals1 vals2 ->
  Forall (fun v : Exp => VALCLOSED v) vals1 /\
  Forall (fun v : Exp => VALCLOSED v) vals2.
Proof.
  induction vals1; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. firstorder.
  * apply element_exist in H as H'. destruct H', H1. subst. inversion H.
    inversion H0. subst. apply Vrel_closed in H5. destruct H5.
    split; constructor; auto.
    - apply (IHvals1 x0); auto.
    - apply (IHvals1 x0); auto.
Qed.

(* Lemma alma :
  forall e ξ x v, 
                  subst (idsubst[[x ::= v]]) (subst (ξ -- [x]) e) =
                  subst (ξ[[x ::= v]]) e.
Proof.
  induction e; intros; subst; try reflexivity.
  * unfold "--", extend_subst. cbn. break_match_goal.
    - break_match_goal.
      + apply var_funid_eqb_eq in Heqb0. subst. cbn. rewrite eqb_refl. auto.
      + apply var_funid_eqb_neq in Heqb0. break_match_hyp.
        ** destruct x.
           -- apply eqb_eq in Heqb1. subst. contradiction.
           -- congruence.
        ** congruence.
    - break_match_goal.
      + apply var_funid_eqb_eq in Heqb0. subst. rewrite eqb_refl in Heqb. congruence.
      + break_match_hyp.
        ** congruence.
        ** destruct x.
           -- apply 
Qed. *)

Lemma Vrel_Fun_compat :
  forall Γ vl b1 b2,
  Erel_open (Γ ++ map inl vl) b1 b2 ->
  Vrel_open Γ (EFun vl b1) (EFun vl b2).
Proof.
  intros. unfold Vrel_open. intros.
  inversion H0 as [? [? ?] ].
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor. eapply subst_preserves_scope_rev; eauto.
  - constructor. eapply subst_preserves_scope_rev; eauto.
  - break_match_goal; try congruence. intros. unfold Erel_open, Erel in H.
    Search subst.
(*     rewrite subst_composition; eauto.
    unfold Erel in H.
    eapply H. unfold Grel. split. 2: split.
    1-2: apply subscoped_ext_app; auto.
    1, 3: rewrite map_length; auto.
    1-2: apply biforall_vrel_helper in H6.
    1-4: try lia; destruct H6; auto.
    intros. unfold substcomp. (* Technical, but doable *)*)
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

