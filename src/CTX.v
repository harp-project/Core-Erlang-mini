(**
  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we define contextual equivalence for sequential Core Erlang.
  We prove the contextual equivalence coincides with CIU equivalence and
  lofical relations.

  At the bottom of the file, we define a notion of behavioural equivalence too,
  which also proved to be coincide with CIU equivalence.
*)
From CoreErlang Require Export CIU.

Import ListNotations.

Definition Adequate (R : nat -> Exp -> Exp -> Prop) :=
  forall e1 e2, R 0 e1 e2 -> |[], e1| ↓ -> |[], e2| ↓.

Definition IsReflexive (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e,
  EXP Γ ⊢ e -> R Γ e e.

Definition CompatibleFun (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ vl vl' e1 e2, vl = vl' ->
    R (S (vl) + Γ) e1 e2 ->
    R Γ (VFun vl e1) (VFun vl' e2).

Definition CompatibleApp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f1 f2 vals1 vals2,
  Forall (fun e => EXP Γ ⊢ e) vals1 -> Forall (fun e => EXP Γ ⊢ e) vals2 ->
  EXP Γ ⊢ f1 -> EXP Γ ⊢ f2 ->
  R Γ f1 f2 -> 
  list_biforall (fun e1 e2 => R Γ e1 e2) vals1 vals2 ->
  R Γ (EApp f1 vals1) (EApp f2 vals2).

Definition CompatibleLet (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP (S Γ) ⊢ e2 -> EXP (S Γ) ⊢ e2' ->
  R Γ e1 e1' -> R (S Γ) e2 e2' ->
  R Γ (ELet e1 e2) (ELet e1' e2').

Definition CompatibleCase (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2' e3 e3' p,
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP pat_vars p + Γ ⊢ e2 -> EXP pat_vars p + Γ ⊢ e2' -> 
  EXP Γ ⊢ e3 -> EXP Γ ⊢ e3' ->
  R Γ e1 e1' -> R (pat_vars p + Γ) e2 e2' -> R Γ e3 e3' ->
  R Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').

Definition CompatibleCons (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
  R Γ e1 e1' -> R Γ e2 e2' ->
  R Γ (ECons e1 e2) (ECons e1' e2').

Definition CompatibleBIF (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f1 f2 vals1 vals2,
  Forall (fun e => EXP Γ ⊢ e) vals1 -> Forall (fun e => EXP Γ ⊢ e) vals2 ->
  EXP Γ ⊢ f1 -> EXP Γ ⊢ f2 ->
  R Γ f1 f2 -> 
  list_biforall (fun e1 e2 => R Γ e1 e2) vals1 vals2 ->
  R Γ (EBIF f1 vals1) (EBIF f2 vals2).

(* TODO: changes *)
Definition CompatibleReceive (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l l2,
  Forall (fun '(p,e) => EXP pat_vars p + Γ ⊢ e) l ->
  Forall (fun '(p,e) => EXP pat_vars p + Γ ⊢ e) l2 ->
  list_biforall (fun '(p1, e1) '(p2, e2) => p1 = p2 /\ R (pat_vars p1 + Γ) e1 e2) l l2 ->
  R Γ (EReceive l) (EReceive l2).

Definition IsPreCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  (forall Γ e1 e2, R Γ e1 e2 -> EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\ CompatibleApp R /\ CompatibleLet R /\
  CompatibleCase R /\ CompatibleCons R /\ CompatibleBIF R /\
  CompatibleReceive R.

Definition IsCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  IsPreCtxRel R /\
  forall R', IsPreCtxRel R' ->
    forall Γ e1 e2, R' Γ e1 e2 -> R Γ e1 e2.

Lemma bigger_implies_IsCtxRel : forall E R,
    IsCtxRel R ->
    IsPreCtxRel E ->
    (forall Γ e1 e2, R Γ e1 e2 -> E Γ e1 e2) ->
    IsCtxRel E.
Proof.
  intros.
  split; auto.
  intros.
  apply H1.
  destruct H.
  eapply H4.
  - exact H2.
  - auto.
Qed.

Theorem Erel_IsPreCtxRel : IsPreCtxRel Erel_open.
Proof.
  unfold IsPreCtxRel.
  intuition idtac.
  * eapply Erel_open_scope in H.
    intuition idtac.
  * eapply Erel_open_scope in H.
    intuition idtac.
  * unfold Adequate.
    intros.
    apply CIU_iff_Erel in H.
    unfold CIU_open, CIU in H.
    specialize (H idsubst (scope_idsubst 0)).
    destruct H, H1. do 2 rewrite idsubst_is_id in H2.
    apply H2.
    now constructor. auto.
  * unfold IsReflexive.
    intros.
    apply Erel_Fundamental.
    auto.
  * unfold Transitive.
    intros.
    apply CIU_iff_Erel.
    apply CIU_iff_Erel in H.
    apply CIU_iff_Erel in H0.
    unfold CIU_open in *.
    intros.
    specialize (H ξ H1).
    specialize (H0 ξ H1).
    unfold CIU in *.
    intuition idtac.
    specialize (H5 F H4).
    specialize (H6 F H4).
    auto.
  * unfold CompatibleFun.
    intros.
    auto.
  * unfold CompatibleApp.
    intros.
    now apply Erel_App_compat.
  * unfold CompatibleLet.
    intros.
    apply Erel_Let_compat; auto.
  * unfold CompatibleCase.
    intros. now apply Erel_Case_compat.
  * unfold CompatibleCons.
    intros. now apply Erel_Cons_compat.
  * unfold CompatibleBIF.
    intros. now apply Erel_BIF_compat.
  * intro. intros. apply Erel_Receive_compat; do 2 constructor.
    - rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in H; intros.
      specialize (H i H2).
      replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
      replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto.
      do 2 rewrite map_nth. destruct (nth i l (PNil, ˝VLit 0%Z)); auto.
    - rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in H0; intros.
      specialize (H0 i H2).
      replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
      replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto.
      do 2 rewrite map_nth. destruct (nth i l2 (PNil, ˝VLit 0%Z)); auto.
Qed.

Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open.
Proof.
  pose proof Erel_IsPreCtxRel.
  unfold IsPreCtxRel in *.
  intuition idtac.
  all: unfold Adequate, Transitive, IsReflexive, CompatibleFun,
    CompatibleApp, CompatibleLet, CompatibleCase, CompatibleCons,
    CompatibleBIF, CompatibleReceive; intros.
  all: try apply CIU_iff_Erel.
  * apply CIU_iff_Erel in H9.
    apply H0 in H9.
    intuition.
  * apply CIU_iff_Erel in H9.
    apply H0 in H9.
    intuition.
  * apply CIU_iff_Erel in H9.
    apply H in H9. auto.
  * now apply H1.
  * apply CIU_iff_Erel in H9.
    apply CIU_iff_Erel in H11.
    eapply H2; eauto.
  * apply CIU_iff_Erel in H11.
    now eapply H3.
  * apply CIU_iff_Erel in H14.
    eapply biforall_impl in H15.
    eapply H4; eauto.
    intros. now apply CIU_iff_Erel.
  * apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    now eapply H5.
  * apply CIU_iff_Erel in H16.
    apply CIU_iff_Erel in H17.
    apply CIU_iff_Erel in H18.
    eapply H6; eauto.
  * apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    now apply H7.
  * apply CIU_iff_Erel in H14.
    eapply biforall_impl in H15.
    eapply H8; eauto.
    intros. now apply CIU_iff_Erel.
  * apply H10. all: auto.
    eapply biforall_impl. 2: exact H12.
    simpl. intros. destruct x, y. split. apply H13. apply CIU_implies_Erel. apply H13.
Qed.

Inductive Ctx :=
| CHole
| CFun      (vl : nat) (e : Ctx)
| CAppFun   (exp : Ctx) (l : list Exp)
| CAppParam (exp : Exp) (l1 : list Exp) (c : Ctx) (l2 : list Exp)  (** one of the middle ones is a ctx *)
| CLet1     (e1 : Ctx) (e2 : Exp)
| CLet2     (e1 : Exp) (e2 : Ctx)
| CCase1    (e1 : Ctx) (p : Pat) (e2 e3 : Exp)
| CCase2    (e1 : Exp) (p : Pat) (e2 : Ctx) (e3 : Exp)
| CCase3    (e1 : Exp) (p : Pat) (e2 : Exp) (e3 : Ctx)
| CCons1    (e1 : Exp) (e2 : Ctx)
| CCons2    (e1 : Ctx) (e2 : Exp)
| CBIFFun   (exp : Ctx) (l : list Exp)
| CBIFParam (exp : Exp) (l1 : list Exp) (c : Ctx) (l2 : list Exp)
| CReceive  (l1 : list (Pat * Exp)) (p : Pat) (c : Ctx) (l2 : list (Pat * Exp))
.

Fixpoint plug (C : Ctx) (p : Exp) :=
match C with
| CHole => p
| CFun vl e => VFun vl (plug e p)
| CAppFun exp l => EApp (plug exp p) l
| CAppParam exp l1 c l2 => EApp exp (l1 ++ [plug c p] ++ l2)
| CLet1 e1 e2 => ELet (plug e1 p) e2
| CLet2 e1 e2 => ELet e1 (plug e2 p)
| CCase1 e1 pat e2 e3 => ECase (plug e1 p) pat e2 e3
| CCase2 e1 pat e2 e3 => ECase e1 pat (plug e2 p) e3
| CCase3 e1 pat e2 e3 => ECase e1 pat e2 (plug e3 p)
| CCons1 e1 e2 => ECons e1 (plug e2 p)
| CCons2 e1 e2 => ECons (plug e1 p) e2
| CBIFFun exp l => EBIF (plug exp p) l
| CBIFParam exp l1 c l2 => EBIF exp (l1 ++ [plug c p] ++ l2)
| CReceive l1 p0 c l2 => EReceive (l1 ++ [(p0, plug c p)] ++ l2)
end.

Fixpoint plugc (Where : Ctx) (p : Ctx) :=
match Where with
| CHole => p
| CFun vl e => CFun vl (plugc e p)
| CAppFun exp l => CAppFun (plugc exp p) l
| CAppParam exp l1 c l2 => CAppParam exp l1 (plugc c p) l2
| CLet1 e1 e2 => CLet1 (plugc e1 p) e2
| CLet2 e1 e2 => CLet2 e1 (plugc e2 p)
| CCase1 e1 pat e2 e3 => CCase1 (plugc e1 p) pat e2 e3
| CCase2 e1 pat e2 e3 => CCase2 e1 pat (plugc e2 p) e3
| CCase3 e1 pat e2 e3 => CCase3 e1 pat e2 (plugc e3 p)
| CCons1 e1 e2 => CCons1 e1 (plugc e2 p)
| CCons2 e1 e2 => CCons2 (plugc e1 p) e2
| CBIFFun exp l => CBIFFun (plugc exp p) l
| CBIFParam exp l1 c l2 => CBIFParam exp l1 (plugc c p) l2
| CReceive l1 p0 c l2 => CReceive l1 p0 (plugc c p) l2
end.

Lemma plug_assoc : forall C1 C2 e,
    plug C1 (plug C2 e) =
    plug (plugc C1 C2) e.
Proof.
  induction C1;
    intros;
    cbn;
    auto;
    rewrite IHC1;
    auto.
Qed.

Reserved Notation "'EECTX' Γh ⊢ C ∷ Γ" (at level 60).
Reserved Notation "'VECTX' Γh ⊢ C ∷ Γ" (at level 60).

Inductive EECtxScope (Γh : nat) : nat -> Ctx -> Prop :=
| CEScope_hole : (EECTX Γh ⊢ CHole ∷ Γh)
| CEScope_App_f : forall Γ C exps,
    EECTX Γh ⊢ C ∷ Γ -> 
    (Forall (fun v => EXP Γ ⊢ v) exps) ->
    EECTX Γh ⊢ CAppFun C exps ∷ Γ
| CEScope_App_v : forall Γ f l1 l2 C,
    EXP Γ ⊢ f ->
    (Forall (fun v => EXP Γ ⊢ v) l1) -> (Forall (fun v => EXP Γ ⊢ v) l2) ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ CAppParam f l1 C l2 ∷ Γ
| CEScope_Let1 : forall Γ C e2,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP (S Γ) ⊢ e2 ->
    EECTX Γh ⊢ CLet1 C e2 ∷ Γ
| CEScope_Let2 : forall Γ e1 C,
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ C ∷ (S Γ) ->
    EECTX Γh ⊢ CLet2 e1 C ∷ Γ
| CEScope_Case1 : forall Γ C e2 e3 p,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP pat_vars p + Γ ⊢ e2 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CCase1 C p e2 e3 ∷ Γ
| CEScope_Case2 : forall Γ C e1 e3 p,
    EECTX Γh ⊢ C ∷ pat_vars p + Γ -> 
    EXP Γ ⊢ e1 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CCase2 e1 p C e3 ∷ Γ
| CEScope_Case3 : forall Γ C e1 e2 p,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e1 ->
    EXP pat_vars p + Γ ⊢ e2 ->
    EECTX Γh ⊢ CCase3 e1 p e2 C ∷ Γ
| CEScope_Cons1 : forall Γ C e1,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ CCons1 e1 C ∷ Γ
| CEScope_Cons2 : forall Γ e2 C,
    EXP Γ ⊢ e2 ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ CCons2 C e2 ∷ Γ
| CEScope_BIF_f : forall Γ C exps,
    EECTX Γh ⊢ C ∷ Γ -> 
    (Forall (fun v => EXP Γ ⊢ v) exps) ->
    EECTX Γh ⊢ CBIFFun C exps ∷ Γ
| CEScope_BIF_v : forall Γ f l1 l2 C,
    EXP Γ ⊢ f ->
    (Forall (fun v => EXP Γ ⊢ v) l1) -> (Forall (fun v => EXP Γ ⊢ v) l2) ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ CBIFParam f l1 C l2 ∷ Γ
| CEScope_Receive : forall Γ l1 l2 p C,
   EECTX Γh ⊢ C ∷ pat_vars p + Γ ->
   (forall i, i < length l1 -> EXP (nth i (map (fst >>> pat_vars) l1) 0) + Γ ⊢ nth i (map snd l1) (˝VLit 0%Z)) ->
   (forall i, i < length l2 -> EXP (nth i (map (fst >>> pat_vars) l2) 0) + Γ ⊢ nth i (map snd l2) (˝VLit 0%Z)) ->
   EECTX Γh ⊢ CReceive l1 p C l2 ∷ Γ
| CEScope_RecFun : forall Γ vl C,
    EECTX Γh ⊢ C ∷ (S vl + Γ) ->
    EECTX Γh ⊢ CFun vl C ∷ Γ
where
"'EECTX' Γh ⊢ C ∷ Γ" := (EECtxScope Γh Γ C).

Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e).
Proof.
  induction C;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    do 2 constructor;
    firstorder idtac.
  * rewrite indexed_to_forall in H5. apply H5; auto.
  * apply nth_possibilities with (def := ˝VLit 0%Z) in H1 as H1'. destruct H1'.
    - destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7; auto.
    - destruct H2. rewrite H2 in *. remember (i - length l1) as i'. destruct i'.
      + simpl. apply IHC; auto.
      + simpl. rewrite indexed_to_forall in H8. apply H8; auto. simpl in H3. lia.
  * rewrite indexed_to_forall in H5. apply H5; auto.
  * apply nth_possibilities with (def := ˝VLit 0%Z) in H1 as H1'. destruct H1'.
    - destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7; auto.
    - destruct H2. rewrite H2 in *. remember (i - length l1) as i'. destruct i'.
      + simpl. apply IHC; auto.
      + simpl. rewrite indexed_to_forall in H8. apply H8; auto. simpl in H3. lia.
  * apply nth_possibilities with (def := (PNil, ˝VLit 0%Z)) in H1 as H1'. destruct H1'.
    - destruct H2.
      assert (nth i (map snd (l1 ++ (p, plug C e) :: l2)) (VLit 0%Z) = nth i (map snd l1) (VLit 0%Z)).
      { replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto. now rewrite map_nth, H2, map_nth. }
      assert (nth i (map (fst >>> pat_vars) (l1 ++ (p, plug C e) :: l2)) 0 = nth i (map (fst >>> pat_vars) l1) 0).
      { replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto. now rewrite map_nth, H2, map_nth. }
      rewrite H4, H6 in *. apply H7; auto.
    - destruct H2.
      assert (nth i (map snd (l1 ++ (p, plug C e) :: l2)) (˝VLit 0%Z) = nth (i - length l1) (map snd ((p, plug C e) :: l2)) (˝VLit 0%Z)).
      { replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto. now rewrite map_nth, H2, map_nth. }
      assert (nth i (map (fst >>> pat_vars) (l1 ++ (p, plug C e) :: l2)) 0 = nth (i - length l1) (map (fst >>> pat_vars) ((p, plug C e) :: l2)) 0).
      { replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto. now rewrite map_nth, H2, map_nth. }
      rewrite H4, H6 in *. remember (i - length l1) as i'. destruct i'.
      + simpl. apply IHC; auto.
      + simpl. apply H8; auto. simpl in H3. lia.
Qed.

Lemma plugc_preserves_scope_exp : forall {Γh Couter Γ Cinner Γ'},
    (EECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     EECTX Γh ⊢ plugc Couter Cinner ∷ Γ).
Proof.
  induction Couter;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
Qed.

Definition CTX (Γ : nat) (e1 e2 : Exp) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ∷ 0 -> | [], plug C e1 | ↓ -> | [], plug C e2| ↓).

Lemma IsReflexiveList : forall R' l Γ',
  IsReflexive R' -> Forall (fun v : Exp => EXP Γ' ⊢ v) l ->
  Forall (fun '(e0, e3) => R' Γ' e0 e3) (combine l l).
Proof.
  induction l; intros; constructor.
  * apply H. inversion H0. auto.
  * inversion H0. apply IHl; auto.
Qed.

Lemma CTX_bigger : forall R' : nat -> Exp -> Exp -> Prop,
    IsPreCtxRel R' -> forall (Γ : nat) (e1 e2 : Exp), R' Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros R' HR.
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet  [ RCase [ RCons [RBIF RReceive ] ] ] ] ] ] ] ] ] ].
  unfold CTX.
  intros.
  destruct (Rscope _ _ _ H) as [Hscope_e1 Hscope_e2].
  intuition idtac. eapply Radequate; eauto.
  assert (forall Γ', EECTX Γ ⊢ C ∷ Γ' -> 
                     R' Γ' (plug C e1) (plug C e2)).
  { clear H0 H1.
    induction C;
      intros;
      inversion H0;
      subst;
      cbn;
      try solve_inversion;
      auto.
    - apply RApp; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inv H0. inv H2. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inv H0. inv H2. by auto.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RApp; auto.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
             simpl in H0. inv H0. inv H5.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (VLit 0%Z). rewrite length_app. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
             simpl in H0. inv H0. inv H5.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (VLit 0%Z). rewrite length_app. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H7. auto.
        ** simpl. apply IHC. auto.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H8. auto.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
    - apply RBIF; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. repeat destruct_scope. by auto.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RBIF; auto.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
             simpl in H0. repeat destruct_scope.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (VLit 0%Z). rewrite length_app. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
             simpl in H0. repeat destruct_scope.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (VLit 0%Z). rewrite length_app. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H7. auto.
        ** simpl. apply IHC. auto.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H8. auto.
    - apply RReceive; auto.
      + apply Forall_app; split. 2: constructor.
        1,3: rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)); intros.
        * apply H7 in H1.
          replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * apply H8 in H1.
          replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + apply Forall_app; split. 2: constructor.
        1,3: rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)); intros.
        * apply H7 in H1.
          replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * apply H8 in H1.
          replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
      + apply biforall_app. 2: constructor.
        * clear H0. (* biforall_refl not sufficient, bc preconditions *)
          induction l1; constructor; auto. 2: apply IHl1; auto.
          destruct a. split; auto. apply Rrefl. apply (H7 0). simpl. lia.
          intros. apply (H7 (S i)). simpl. lia.
        * split; auto.
        * clear H0. induction l2; constructor; auto. 2: apply IHl2; auto.
          destruct a. split; auto. apply Rrefl. apply (H8 0). simpl. lia.
          intros. apply (H8 (S i)). simpl. lia.
  }
  now apply H2.
Qed.

Theorem CTX_refl Γ e : EXP Γ ⊢ e -> CTX Γ e e.
Proof.
  unfold CTX. intros. split; auto.
Qed.

Lemma PreCTX_app_helper : forall vals1 vals1' C Γ x f2 vals2 (HC: EECTX Γ ⊢ C ∷ 0) (f2S : EXP Γ ⊢ f2),
  | [], plug C (plug (CAppParam f2 vals2 CHole vals1) x) | ↓ ->
  list_biforall
  (fun e1 e2 : Exp =>
   (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
   (forall C : Ctx, EECTX Γ ⊢ C ∷ 0 -> | [], plug C e1 | ↓ -> | [], plug C e2 | ↓)) vals1 vals1' ->
   Forall (fun e : Exp => EXP Γ ⊢ e) vals1 ->
   Forall (fun e : Exp => EXP Γ ⊢ e) vals2 ->
   EXP Γ ⊢ x
->
  | [], plug C (EApp f2 (vals2 ++ [x] ++ vals1')) | ↓.
Proof.
  induction vals1; intros.
  * inversion H0. subst. rewrite app_nil_r. simpl in H. auto.
  * inversion H0. inversion H1. subst. destruct H6, H4.
    rewrite app_cons_swap. rewrite app_assoc. eapply IHvals1; eauto.
    simpl in H.
    assert (EECTX Γ ⊢ plugc C (CAppParam f2 (vals2 ++ [x]) CHole vals1) ∷ 0) as HC2. {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. apply Forall_app. split; auto. constructor.
    }
    apply H5 in HC2.
    2: { rewrite <- plug_assoc. simpl. now rewrite app_cons_swap, app_assoc in H. }
    simpl. rewrite <- plug_assoc in HC2. now simpl in HC2.
    apply Forall_app. split; auto.
Qed.

Lemma PreCTX_BIF_helper : forall vals1 vals1' C Γ x f2 vals2 (HC: EECTX Γ ⊢ C ∷ 0) (f2S : EXP Γ ⊢ f2),
  | [], plug C (plug (CBIFParam f2 vals2 CHole vals1) x) | ↓ ->
  list_biforall
  (fun e1 e2 : Exp =>
   (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
   (forall C : Ctx, EECTX Γ ⊢ C ∷ 0 -> | [], plug C e1 | ↓ -> | [], plug C e2 | ↓)) vals1 vals1' ->
   Forall (fun e : Exp => EXP Γ ⊢ e) vals1 ->
   Forall (fun e : Exp => EXP Γ ⊢ e) vals2 ->
   EXP Γ ⊢ x
->
  | [], plug C (EBIF f2 (vals2 ++ [x] ++ vals1')) | ↓.
Proof.
  induction vals1; intros.
  * inversion H0. subst. rewrite app_nil_r. simpl in H. auto.
  * inversion H0. inversion H1. subst. destruct H6, H4.
    rewrite app_cons_swap. rewrite app_assoc. eapply IHvals1; eauto.
    simpl in H.
    assert (EECTX Γ ⊢ plugc C (CBIFParam f2 (vals2 ++ [x]) CHole vals1) ∷ 0) as HC2. {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. apply Forall_app. split; auto. constructor.
    }
    apply H5 in HC2.
    2: { rewrite <- plug_assoc. simpl. now rewrite app_cons_swap, app_assoc in H. }
    simpl. rewrite <- plug_assoc in HC2. now simpl in HC2.
    apply Forall_app. split; auto.
Qed.

(* Local Definition dummyv := "foo"%string.
Local Definition dummyf := ("foo"%string, 0).

Fixpoint default_names (e : Exp) : Exp :=
match e with
 | VLit l => e
 | VPid p => e
 | VVar n => VVar n
 | VFun vl e => VFun (map (fun _ => dummyv) vl) (default_names e)
 | EApp exp l => EApp (default_names exp) (map default_names l)
 | ELet v e1 e2 => ELet dummyv (default_names e1) (default_names e2)
 | ELetRec f vl b e => ELetRec dummyf (map (fun _ => dummyv) vl) (default_names b) (default_names e)
 | ECase e1 p e2 e3 => ECase (default_names e1) p (default_names e2) (default_names e3)
 | ECons e1 e2 => ECons (default_names e1) (default_names e2)
 | VNil => VNil
 | VCons e1 e2 => VCons (default_names e1) (default_names e2)
 | EBIF exp l => EBIF (default_names exp) (map default_names l)
 | EReceive l => EReceive (map (fun '(p, e) => (p, default_names e)) l)
end.

Lemma default_scope : forall Γ,
  (forall e, VAL Γ ⊢ e -> VAL Γ ⊢ (default_names e)) /\
  (forall e, EXP Γ ⊢ e -> EXP Γ ⊢ (default_names e)).
Proof.
  apply scoped_ind; intros; cbn; constructor; auto.
  * now rewrite length_map.
  * intros. replace (VLit 0%Z) with (default_names (VLit 0%Z)) by auto. rewrite map_nth.
    apply H0. now rewrite length_map in H1.
  * now rewrite length_map.
  * intros. replace (VLit 0%Z) with (default_names (VLit 0%Z)) by auto. rewrite map_nth.
    apply H0. now rewrite length_map in H1.
  * intros. rewrite length_map in H0. apply H in H0.
    rewrite map_map.
    replace (fun x : Pat * Exp => (fst >>> pat_vars) (let '(p, e0) := x in (p, default_names e0))) with
            (@fst Pat Exp >>> pat_vars).
    rewrite map_map.
    replace (fun x : Pat * Exp => snd (let '(p, e0) := x in (p, default_names e0))) with
            (@snd Pat Exp >>> default_names).
    replace (VLit 0%Z) with (default_names (VLit 0%Z)) in H0 by auto. rewrite <- (map_nth default_names) in H0.
    rewrite map_map in H0. exact H0.
    all: extensionality x; cbn; destruct x; reflexivity.
Qed.

Corollary default_value : forall Γ,
  forall e, VAL Γ ⊢ e -> VAL Γ ⊢ (default_names e).
Proof.
  intros. now apply default_scope.
Qed.

Corollary default_exp : forall Γ,
  forall e, EXP Γ ⊢ e -> EXP Γ ⊢ (default_names e).
Proof.
  intros. now apply default_scope.
Qed.

Global Hint Resolve default_value : core.
Global Hint Resolve default_exp : core.

Lemma default_scope_rev : forall e Γ,
  (VAL Γ ⊢ default_names e -> VAL Γ ⊢ e) /\
  (EXP Γ ⊢ default_names e -> EXP Γ ⊢ e).
Proof.
  induction e using Exp_ind2 with 
    (Q := fun l => Forall (fun e => forall Γ, 
                                 (VAL Γ ⊢ default_names e -> VAL Γ ⊢ e) /\
                                 (EXP Γ ⊢ default_names e -> EXP Γ ⊢ e)) 
                          l)
    (W := fun l => Forall (fun '(_, e) => forall Γ, 
                                 (VAL Γ ⊢ default_names e -> VAL Γ ⊢ e) /\
                                 (EXP Γ ⊢ default_names e -> EXP Γ ⊢ e)) 
                          l);
    intros; auto; split; intro; simpl in *; try inversion_is_value.
  * constructor. inversion H. subst. rewrite length_map in H1. now apply IHe in H1.
  * do 2 constructor.
    inversion H. inversion H0. subst. rewrite length_map in H3. now apply IHe in H3.
  * inversion H; subst. constructor.
    - now apply IHe in H2.
    - intros. rewrite length_map in H3. specialize (H3 i H0).
      rewrite indexed_to_forall in IHe0.
      replace (VLit 0%Z) with (default_names (VLit 0%Z)) in H3 by auto.
      rewrite map_nth in H3. now apply IHe0 in H3.
    - inversion_is_value.
  * inversion H; subst. constructor.
    - now apply IHe1 in H2.
    - now apply IHe2 in H4.
    - inversion_is_value.
  * inversion H; subst. constructor.
    - rewrite length_map in H2. now apply IHe1 in H2.
    - now apply IHe2 in H5.
    - inversion_is_value.
  * inversion H; subst. constructor.
    - now apply IHe1 in H3.
    - now apply IHe2 in H5.
    - now apply IHe3 in H6.
    - inversion_is_value.
  * inversion H; subst. constructor.
    - now apply IHe1 in H2.
    - now apply IHe2 in H3.
    - inversion_is_value.
  * inversion H; subst. constructor.
    - now apply IHe1 in H2.
    - now apply IHe2 in H3.
  * inversion H; inversion H0; subst. do 2 constructor.
    - now apply IHe1 in H4.
    - now apply IHe2 in H5.
  * inversion H; subst. constructor.
    - now apply IHe in H2.
    - intros. rewrite length_map in H3. specialize (H3 i H0).
      rewrite indexed_to_forall in IHe0.
      replace (VLit 0%Z) with (default_names (VLit 0%Z)) in H3 by auto.
      rewrite map_nth in H3. now apply IHe0 in H3.
    - inversion_is_value.
  * inversion H. 2: inversion H0. subst.
    constructor. intros.
    rewrite (indexed_to_forall _ _ (PNil, VLit 0%Z)) in IHe. apply IHe in H0 as H01.
    rewrite length_map in H1. apply H1 in H0.
    replace (VLit 0%Z) with (snd (PNil, VLit 0%Z)) by auto.
    replace 0 with ((@fst Pat Exp >>> pat_vars) (PNil, VLit 0%Z)) by auto.
    replace (VLit 0%Z) with (snd (PNil, VLit 0%Z)) in H0 by auto.
    replace 0 with ((@fst Pat Exp >>> pat_vars) (PNil, VLit 0%Z)) in H0 by auto.

    do 2 rewrite map_nth. do 2 rewrite map_nth in H0.
    destruct (nth i l (PNil, VLit 0%Z)) eqn:EQ.
    apply H01.
    epose proof (map_nth (fun '(p, e) => (p, default_names e)) l (PNil, VLit 0%Z) i). simpl in H2.
    rewrite H2 in H0. rewrite EQ in H0. cbn in *. auto.
Qed.

Corollary default_value_rev : forall Γ,
  (forall e, VAL Γ ⊢ default_names e -> VAL Γ ⊢ e).
Proof.
  intros. now apply default_scope_rev.
Qed.

Corollary default_exp_rev : forall Γ,
  (forall e, EXP Γ ⊢ default_names e -> EXP Γ ⊢ e).
Proof.
  intros. now apply default_scope_rev.
Qed.

Global Hint Resolve default_value_rev : core.
Global Hint Resolve default_exp_rev : core.

(* Lemma default_names_helper l:
  (forall e : Exp, In e l -> is_value e)
->
  (forall e : Exp, In e (map default_names l) -> is_value e).
Proof.
  induction l; intros; subst. inversion H0.
  destruct (In_dec Exp_eq_dec e (map default_names l)) eqn:P.
  * apply IHl. intros. apply H. now constructor 2. clear P. auto.
  * inversion H0. 2: congruence. subst.
    epose proof (H a _). now apply -> default_value. Unshelve. constructor. auto.
Qed. *)

Definition default_name_frame (f : Frame) : Frame :=
match f with
 | FApp1 l => FApp1 (map default_names l)
 | FApp2 v l1 l2 => 
          FApp2 (default_names v) (map default_names l1) (map default_names l2)
 | FLet v e2 => FLet dummyv (default_names e2)
 | FCase p e2 e3 => FCase p (default_names e2) (default_names e3)
 | FCons1 e => FCons1 (default_names e)
 | FCons2 e => FCons2 (default_names e)
 | FBIF1 l => FBIF1 (map default_names l)
 | FBIF2 v l1 l2 => 
          FBIF2 (default_names v) (map default_names l1) (map default_names l2)
end.

Lemma double_default e :
  default_names e = default_names (default_names e).
Proof.
  induction e using Exp_ind2 with 
    (Q := fun l => Forall (fun e => default_names e = default_names (default_names e)) l)
    (W := fun l => Forall (fun '(p, e) => (p, default_names e) = (p, default_names (default_names e))) l); auto.
  * simpl. rewrite map_map, <- IHe. auto.
  * simpl. erewrite map_map, <- IHe. erewrite map_ext_Forall. 2: exact IHe0. auto.
  * simpl. rewrite <- IHe1, <- IHe2. auto.
  * simpl. rewrite <- IHe1, <- IHe2, map_map. auto.
  * simpl. rewrite <- IHe1, <- IHe2, <- IHe3. auto.
  * simpl. rewrite <- IHe1, <- IHe2. auto.
  * simpl. rewrite <- IHe1, <- IHe2. auto.
  * simpl. erewrite map_map, <- IHe. erewrite map_ext_Forall. 2: exact IHe0. auto.
  * simpl. erewrite map_map. erewrite map_ext_Forall. reflexivity.
    induction l; auto. inversion IHe; subst.
    constructor; auto. destruct a; auto.
  * constructor; auto. rewrite <- IHe. auto.
Qed.

Definition default_names_sub (ξ : Substitution) : Substitution :=
  fun n => match (ξ n) with
           | inl exp => inl (default_names exp)
           | inr n' => inr n'
           end.

Lemma rename_id_default :
  forall e ρ, rename ρ (default_names e) = default_names (rename ρ e).
Proof.
  induction e using Exp_ind2 with
    (Q := fun l => forall ρ, Forall (fun e => rename ρ (default_names e) = default_names (rename ρ e)) l)
    (W := fun l => forall ρ, Forall (fun '(p,e) => (p, rename ρ (default_names e)) = (p, default_names (rename ρ e))) l); intros; auto; simpl.
  * f_equiv. now rewrite IHe, length_map.
  * rewrite IHe, map_map, map_map. erewrite map_ext_Forall. 2: apply IHe0. reflexivity.
  * now rewrite IHe1, IHe2.
  * now rewrite length_map, IHe1, IHe2.
  * now rewrite IHe1, IHe2, IHe3.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * rewrite IHe, map_map, map_map. erewrite map_ext_Forall. 2: apply IHe0. reflexivity.
  * rewrite map_map, map_map. erewrite map_ext_Forall. reflexivity.
    induction l; auto.
    constructor; auto.
    - destruct a. specialize (IHe (uprenn (pat_vars p) ρ)). inversion IHe; subst. auto.
    - apply IHl. intros. specialize (IHe ρ0). inversion IHe. apply H2.
  * constructor; auto. now rewrite IHe.
Qed.

Lemma default_names_up :
  forall ξ, up_subst (default_names_sub ξ) = default_names_sub (up_subst ξ).
Proof.
  intros. unfold up_subst, default_names_sub, shift. extensionality x. destruct x; auto.
  destruct (ξ x); auto. rewrite rename_id_default. auto.
Qed.

Corollary default_names_upn :
  forall n ξ, upn n (default_names_sub ξ) = default_names_sub (upn n ξ).
Proof.
  induction n; auto.
  intros. simpl. rewrite <- default_names_up, IHn. auto.
Qed.

Lemma alpha_helper : forall e2 ξ,
  default_names e2.[ξ] = (default_names e2).[default_names_sub ξ].
Proof.
  induction e2 using Exp_ind2 with
    (Q := fun l => forall ξ, Forall (fun e2 => default_names e2.[ξ] = (default_names e2).[default_names_sub ξ]) l)
    (W := fun l => forall ξ, Forall (fun '(p, e2) => (p,default_names e2.[ξ]) = (p, (default_names e2).[default_names_sub ξ])) l); intros; simpl; auto.
  * unfold default_names_sub; destruct (ξ n); auto; apply double_default.
  * unfold default_names_sub; destruct (ξ n); auto; apply double_default.
  * simpl. f_equiv. rewrite default_names_upn, default_names_up, IHe2. rewrite length_map. auto.
  * simpl. rewrite IHe2, map_map, map_map. erewrite map_ext_Forall. reflexivity. apply IHe0.
  * now rewrite IHe2_1, default_names_up, IHe2_2.
  * rewrite length_map. now rewrite default_names_upn, default_names_up, IHe2_1, default_names_up, IHe2_2.
  * now rewrite IHe2_1, default_names_upn, IHe2_2, IHe2_3.
  * now rewrite IHe2_1, IHe2_2.
  * now rewrite IHe2_1, IHe2_2.
  * simpl. rewrite IHe2, map_map, map_map. erewrite map_ext_Forall. reflexivity. apply IHe0.
  * erewrite map_map, map_map, map_ext_Forall. reflexivity.
    induction l; auto. constructor.
    - destruct a. specialize (IHe2 (upn (pat_vars p) ξ)). inversion IHe2. subst. 
      rewrite default_names_upn. auto.
    - apply IHl. intros. specialize (IHe2 ξ0). now inversion IHe2.
  * constructor; auto. now rewrite IHe2.
Qed.

Lemma alpha_list_subst :
  forall l ξ, default_names_sub (list_subst l ξ) =
              list_subst (map default_names l) (default_names_sub ξ).
Proof.
  induction l; intros; auto.
  cbn. unfold list_subst in IHl at 2. rewrite <- IHl.
  extensionality n. unfold default_names_sub, list_subst. destruct n; auto.
Qed.

Lemma alpha_id :
  idsubst = default_names_sub idsubst.
Proof.
  unfold idsubst, default_names_sub. auto.
Qed.

Lemma scons_alpha : forall e,
  default_names e .: idsubst = default_names_sub (e .: idsubst).
Proof.
  intros. extensionality n; destruct n; auto.
Qed.

Lemma match_pattern_default :
  forall e p l Γ, VAL Γ ⊢ e -> match_pattern p e = Some l ->
   match_pattern p (default_names e) = Some (map default_names l).
Proof.
  induction e; intros.
  1,3-14: destruct p. all: cbn; auto; inversion H0; auto; try inversion_is_value.
  * break_match_hyp; subst. inversion H2. subst; auto. congruence. 
  * break_match_hyp. break_match_hyp. 2-3: congruence.
    inversion H. subst.
    inversion H2. subst. eapply IHe1 in Heqo; eauto. eapply IHe2 in Heqo0; eauto.
    now rewrite Heqo, Heqo0, map_app.
  * destruct p0; cbn; auto; try inversion_is_value; inversion H0.
    - break_match_hyp; subst. inversion H3. subst; auto. congruence.
    - subst. auto.
Qed.

Lemma nomatch_pattern_default :
  forall e p Γ, VAL Γ ⊢ e -> match_pattern p e = None <->
   match_pattern p (default_names e) = None.
Proof.
  induction e; intros; destruct p; cbn; auto; split; intro; inversion H0; auto; try inversion_is_value.
  * break_match_hyp; inversion H0; auto.
  * break_match_hyp; inversion H0; auto.
  * break_match_hyp. break_match_hyp. congruence.
    - inversion H. subst. eapply IHe2 in Heqo0; eauto. rewrite Heqo0. break_match_goal; auto.
    - inversion H. subst. eapply IHe1 in Heqo; eauto. rewrite Heqo. auto.
  * break_match_hyp. break_match_hyp. congruence.
    - inversion H. subst. eapply IHe2 in Heqo0; eauto. rewrite Heqo0. break_match_goal; auto.
    - inversion H. subst. eapply IHe1 in Heqo; eauto. rewrite Heqo. auto.
Qed.

Lemma match_pattern_default_exists :
  forall e p l Γ, VAL Γ ⊢ e -> match_pattern p (default_names e) = Some l ->
  exists l', l = map default_names l' /\ match_pattern p e = Some l'.
Proof.
  induction e; intros. 1,3-14: destruct p; cbn; auto; inversion H0; auto; try inversion_is_value.
  * break_match_hyp; inversion H2; subst. now exists [].
  * now exists [VLit l].
  * now exists [VVar n].
  * now exists [VFunId n].
  * now exists [VFun vl e].
  * now exists [VNil].
  * now exists [].
  * now exists [VCons e1 e2].
  * break_match_hyp. break_match_hyp. 2-3: congruence. inversion H2.
    inversion H. subst. eapply IHe1 in Heqo; eauto. eapply IHe2 in Heqo0; eauto.
    destruct Heqo, Heqo0, H1, H3. subst. exists (x ++ x0). rewrite map_app. split; auto.
    rewrite H4, H7. auto.
  * destruct p0; inversion H0.
    - break_match_hyp; try congruence. inversion H2. subst. exists []. split; auto.
    - subst. exists [VPid p]; split; auto.
Qed.

Theorem alpha_eval_k :
  forall k e fs, | fs, e | k ↓ <-> | map default_name_frame fs, default_names e | k ↓.
Proof.
  split.
  { generalize dependent e. generalize dependent fs.
    induction k; intros; simpl; inversion H; subst.
    * constructor. now apply default_value.
    * simpl. eapply term_case_true. auto. eapply match_pattern_default. exact H1. exact H2.
      apply IHk in H5. rewrite alpha_helper in H5. rewrite alpha_list_subst in H5.
      now replace (default_names_sub idsubst) with idsubst in H5.
    * apply term_case_false; auto. apply -> nomatch_pattern_default. exact H2. eauto.
    * simpl. constructor; auto. apply IHk in H4. rewrite alpha_helper in H4.
      replace (default_names e .: idsubst) with (default_names_sub (e .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto. apply IHk in H3. rewrite alpha_helper in H3.
      replace (VFun (map (fun _ : Var => dummyv) vl)
                      (default_names b) .: idsubst) with (default_names_sub (VFun vl b .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto. now apply IHk in H4.
    * simpl. constructor; auto. apply IHk in H4. now simpl in H4.
    * simpl. constructor; auto. apply IHk in H3. rewrite alpha_helper in H3.
      replace (VFun [] (default_names e0) .: idsubst) with (default_names_sub (VFun [] e0 .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto.
      - apply Forall_map; auto. eapply Forall_impl. 2: exact H2. intros. apply default_value. auto.
      - apply IHk in H5. simpl in H5. rewrite map_app in H5. auto.
    * simpl. constructor; auto.
      - apply Forall_map; auto. eapply Forall_impl. 2: exact H2. intros. apply default_value. auto.
      - apply IHk in H5. simpl in H5. rewrite map_app in H5. auto.
    * simpl. constructor; auto.

      - apply IHk in H3. exact H3.
    * simpl. constructor; auto.
      - apply Forall_map; auto. eapply Forall_impl. 2: exact H2. intros. apply default_value. auto.
      - do 2 rewrite length_map. lia.
      - apply IHk in H6. rewrite alpha_helper in H6.
        replace (list_subst
                      (VFun (map (fun _ : Var => dummyv) vl)
                         (default_names e0)
                       :: map default_names vs ++ [default_names e])
                      idsubst) with (default_names_sub
                           (list_subst (VFun vl e0 :: vs ++ [e])
                              idsubst)). auto.
        replace [default_names e] with (map default_names [e]) by auto.
        rewrite <- map_app, alpha_list_subst. auto.
    * simpl. constructor; auto. apply IHk in H4. exact H4.
    * simpl. constructor; auto. apply IHk in H5. exact H5.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
  }
  { generalize dependent e. generalize dependent fs.
    induction k; intros; simpl; inversion H; subst.
    * apply eq_sym, map_eq_nil in H0. subst. constructor. auto.
    * destruct fs; inversion H0. destruct f; inversion H4.
      subst. eapply match_pattern_default_exists in H3 as H3'.
      2: { apply default_value_rev in H2. exact H2. } destruct H3' as [l' [EQ1 EQ2]]. subst.
      replace idsubst with (default_names_sub idsubst) in H5 by auto.
      rewrite  <- alpha_list_subst, <- alpha_helper in H5.
      apply IHk in H5. eapply term_case_true; auto.
      2: exact H5. auto.
    * destruct fs; inversion H0. destruct f; inversion H4.
      subst. apply IHk in H5. apply term_case_false; auto.
      rewrite nomatch_pattern_default; eauto.
    * destruct fs; inversion H0. destruct f; inversion H3; subst.
      apply default_value in H2. constructor; auto. apply IHk.
      now rewrite alpha_helper, <- scons_alpha.
    * destruct e; inversion H0; subst. constructor. apply IHk.
      now rewrite alpha_helper, <- scons_alpha.
    * destruct fs; inversion H0. destruct f; inversion H3. destruct l; inversion H6.
      subst. apply term_app_start; auto.
    * destruct fs; inversion H0. destruct f; inversion H3. destruct l; inversion H6.
      subst. apply term_bif_start; auto.
    * destruct e; inversion H1. destruct fs; inversion H0. destruct f; inversion H6.
      subst. destruct l; inversion H8. inversion H1. destruct vl; inversion H4.
      constructor. apply IHk. now rewrite alpha_helper, <- scons_alpha.
    * destruct fs; inversion H0. destruct f; inversion H4. destruct l1; inversion H8.
      subst. apply default_value in H2. apply default_value in H'.
      constructor; auto. eapply map_Forall; eauto.
      apply IHk. simpl. rewrite map_app. auto.
    * destruct fs; inversion H0. destruct f; inversion H4. destruct l1; inversion H8.
      subst. apply default_value in H2. apply default_value in H'.
      constructor; auto. eapply map_Forall; eauto.
      apply IHk. simpl. rewrite map_app. auto.
    * destruct fs; inversion H0. destruct f; inversion H4. destruct l1; inversion H7.
      destruct v; inversion H6.
      destruct l2; inversion H8. subst.
      destruct l2; inversion H11.
      destruct e, e0; simpl default_names in *; try congruence.
      destruct l, l0; try congruence.
      apply term_plus. apply IHk.
      inversion H10. inversion H1. now subst.
    * destruct fs; inversion H0. destruct f; inversion H5. destruct l1; inversion H9.
      destruct v; inversion H8. subst. apply default_value in H4. constructor; auto.
      eapply map_Forall. 2: exact H2.
      do 2 rewrite length_map in H3. auto.
      do 2 rewrite length_map in H3. lia.
      apply IHk. rewrite alpha_helper, alpha_list_subst. simpl. now rewrite map_app.
    * destruct fs; simpl in H0; inversion H0. subst.
      destruct f; inversion H3; subst. apply default_value_rev in H2.
      constructor; auto.
    * destruct fs; simpl in H0; inversion H0. subst.
      destruct f; inversion H4; subst. apply default_value_rev in H3.
      constructor; auto.
    * destruct e; inversion H0. constructor. subst. now apply IHk.
    * destruct e; inversion H0. constructor. subst. now apply IHk.
    * destruct e; inversion H0. constructor. subst. now apply IHk.
    * destruct e; inversion H0. constructor. subst. now apply IHk.
    * destruct e; inversion H0. constructor. subst. now apply IHk.
  }
Qed.

Corollary alpha_eval :
  forall e fs, | fs, e | ↓ <-> | map default_name_frame fs, default_names e | ↓.
Proof.
  intros. split; intros; destruct H; apply alpha_eval_k in H; exists x; auto.
Qed.

Theorem default_context C : forall e,
  default_names (plug C e) = default_names (plug C (default_names e)).
Proof.
  induction C; intros; simpl; auto; try now rewrite IHC.
  * apply double_default.
  * do 2 rewrite map_app. simpl. now rewrite IHC.
  * do 2 rewrite map_app. simpl. now rewrite IHC.
  * do 2 rewrite map_app. simpl. now rewrite IHC.
Qed. *)

Lemma PreCTX_rec_helper : forall vals1 vals1' C Γ x p vals2 (HC: EECTX Γ ⊢ C ∷ 0)
   (Wfvals2 : Forall (fun '(p, e) => EXP pat_vars p + Γ ⊢ e) vals2),
  | [], plug C (plug (CReceive vals2 p CHole vals1) x) | ↓ ->
  list_biforall
  (fun '(p1,e1) '(p2,e2) =>
   p1 = p2 /\ (EXP pat_vars p1 + Γ ⊢ e1 /\ EXP pat_vars p1 + Γ ⊢ e2) /\
   (forall C : Ctx, EECTX pat_vars p1 + Γ ⊢ C ∷ 0 -> | [], plug C e1 | ↓ -> | [], plug C e2 | ↓)) vals1 vals1' ->
   EXP pat_vars p + Γ ⊢ x
->
  | [], plug C (EReceive (vals2 ++ [(p,x)] ++ vals1')) | ↓.
Proof.
  induction vals1; intros.
  * inversion H0. subst. rewrite app_nil_r. simpl in H. auto.
  * inversion H0. destruct H. subst. destruct a, hd'. clear H0. destruct H4 as [H4_1 [[H4_21 H4_22] H4_3]].
    rewrite app_cons_swap, app_assoc.
    specialize (IHvals1 tl' C Γ e0 p1 (vals2 ++ [(p, x)]) HC). apply IHvals1; eauto.
    { apply Forall_app. split; auto. }
    simpl in H. subst. simpl.
    rewrite <- app_assoc, <- app_cons_swap. 
    assert (EECTX pat_vars p1 + Γ ⊢ plugc C (CReceive (vals2 ++ [(p,x)]) p1 CHole vals1) ∷ 0) as HC2. {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. do 2 constructor.
      * replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
        replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto. intros.
        do 2 rewrite map_nth.
        apply nth_possibilities with (def := (PNil, ˝VLit 0%Z)) in H0 as [[? ?] | [? ?]].
        - rewrite H0. rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in Wfvals2. specialize (Wfvals2 i H2).
          break_match_hyp. auto.
        - rewrite H0. destruct (i - length vals2). cbn. auto. simpl in H2. lia.
      * intros.
        replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
        replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto.
        do 2 rewrite map_nth.
        rewrite (indexed_to_biforall _ _ _ (PNil, ˝VLit 0%Z)) in H6. destruct H6.
        specialize (H2 i H0). do 2 break_match_hyp. apply H2.
    }
    apply H4_3 in HC2.
    2: { rewrite <- plug_assoc. simpl. rewrite <- app_assoc, <- app_cons_swap. eexists. exact H. }
    simpl. rewrite <- plug_assoc in HC2. simpl in HC2.
    rewrite <- app_assoc, <- app_cons_swap in HC2. exact HC2.
    subst. auto.
  Unshelve. exact (PNil, ˝VLit 0%Z).
Qed.

Lemma CTX_IsPreCtxRel : IsPreCtxRel CTX.
Proof.
  unfold IsPreCtxRel.
  intuition idtac;
    try solve
        [unfold CTX in H; intuition idtac
        |inversion H; [|constructor]; apply H0].
  * unfold Adequate.
    intros.
    unfold CTX in H.
    intuition idtac.
    - apply (H2 CHole); auto.
      constructor.
  * unfold IsReflexive.
    intros.
    unfold CTX.
    intuition (auto using Rbar_le_refl).
  * unfold Transitive.
    intros.
    unfold CTX in *.
    intuition idtac.
    auto.
  * unfold CompatibleFun.
    intros.
    unfold CTX in *.
    intuition auto.
    do 2 constructor; now try rewrite <- H.
    specialize (H2 (plugc C (CFun vl' CHole))).
    repeat rewrite <- plug_assoc in H2.
    cbn in H2.
    apply H2.
    eapply plugc_preserves_scope_exp; eauto. rewrite H.
    do 2 constructor.
    rewrite <- H. assumption.
  * unfold CompatibleApp.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: rewrite indexed_to_forall in H, H0; constructor; auto.
    clear H3 H7.
    assert (EECTX Γ ⊢ plugc C (CAppFun CHole vals1) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply biforall_length in H4 as LL. rewrite <- plug_assoc in HC_e1.
    destruct vals1; intros.
    - inversion H4. now subst.
    - inversion H4. subst. destruct H9, H3. inversion H. inversion H0. subst.
      assert (EECTX Γ ⊢ plugc C (CAppParam f2 [] CHole vals1) ∷ 0). {
        eapply plugc_preserves_scope_exp; eauto.
        constructor; auto.
        constructor.
      }
      apply H7 in H10. 2: now rewrite <- plug_assoc.
      replace (hd' :: tl') with ([] ++ [hd'] ++ tl') by auto.
      eapply PreCTX_app_helper; eauto.
      now rewrite plug_assoc.
  * unfold CompatibleLet.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H5 H9 H4 H8.
    assert (EECTX Γ ⊢ plugc C (CLet1 CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX S Γ ⊢ plugc C (CLet2 e1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply H7 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2.
    assumption.
  * unfold CompatibleCase.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H7 H12 H8 H13 H5 H14.
    assert (EECTX Γ ⊢ plugc C (CCase1 CHole p e2 e3) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H9 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX pat_vars p + Γ ⊢ plugc C (CCase2 e1' p CHole e3) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H10 in HC_e2. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    assert (EECTX Γ ⊢ plugc C (CCase3 e1' p e2' CHole) ∷ 0) as HC_e3.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H11 in HC_e3. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    rewrite <- plug_assoc in HC_e3. simpl in HC_e3. auto.
  * unfold CompatibleCons.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H4 H8 H5 H9.
    assert (EECTX Γ ⊢ plugc C (CCons1 e1 CHole) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H7 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX Γ ⊢ plugc C (CCons2 CHole e2') ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2; auto.
  * unfold CompatibleBIF.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: rewrite indexed_to_forall in H, H0; constructor; auto.
    clear H3 H7.
    assert (EECTX Γ ⊢ plugc C (CBIFFun CHole vals1) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply biforall_length in H4 as LL. rewrite <- plug_assoc in HC_e1.
    destruct vals1; intros.
    - inversion H4. now subst.
    - inversion H4. subst. destruct H9, H3. inversion H. inversion H0. subst.
      assert (EECTX Γ ⊢ plugc C (CBIFParam f2 [] CHole vals1) ∷ 0). {
        eapply plugc_preserves_scope_exp; eauto.
        constructor; auto.
        constructor.
      }
      apply H7 in H10. 2: now rewrite <- plug_assoc.
      replace (hd' :: tl') with ([] ++ [hd'] ++ tl') by auto.
      eapply PreCTX_BIF_helper; eauto.
      now rewrite plug_assoc.
  * unfold CompatibleReceive.
    intros.
    unfold CTX in *.
    split. split.
    (** TODO: will be changed *)
    3: { intros. destruct l, l2. 2-3: inversion H1.
         auto.
         destruct p, p0. inversion H1. subst. destruct H7 as [H7_1 [ [H7_21 H7_22] H7_3]].
         pose proof (PreCTX_rec_helper l l2 C Γ e p [] H2 ltac:(constructor) H3 H9 H7_21).
         simpl in H4. subst.
         epose proof (P := H7_3 (plugc C (CReceive [] p0 CHole l2)) _). do 2 rewrite <- plug_assoc in P.
         simpl in P. apply P. auto.
        }
    all: rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in H;
    rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in H0.
    all: do 2 constructor; intros.
    all: replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
    all: replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto.
    all: do 2 rewrite map_nth.
    apply H in H2. 2: apply H0 in H2.
    all: break_match_hyp; apply H2.
  Unshelve.
    1-4: exact (˝VNil).
    eapply plugc_preserves_scope_exp. exact H2. constructor. constructor.
    intros. inversion H5.
    intros. rewrite (indexed_to_forall _ _ (PNil, ˝VLit 0%Z)) in H0.
    specialize (H0 (S i) ltac:(simpl;lia)).
    simpl in H0.
    replace (˝VLit 0%Z) with (snd (PNil, ˝VLit 0%Z)) by auto.
    replace 0 with ((fst >>> pat_vars) (PNil, ˝VLit 0%Z)) by auto.
    do 2 rewrite map_nth.
    break_match_hyp; cbn. auto.
Qed.

Lemma CTX_IsCtxRel : IsCtxRel CTX.
Proof.
  unfold IsCtxRel.
  split.
  - apply CTX_IsPreCtxRel.
  - intros.
    eapply CTX_bigger; eauto.
Qed.

Global Hint Resolve CTX_IsCtxRel : core.
Global Hint Resolve CTX_IsPreCtxRel : core.

Corollary CIU_implies_CTX :
  forall Γ e1 e2, CIU_open Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros. eapply CTX_bigger. 2: exact H. apply CIU_IsPreCtxRel.
Qed.

Global Hint Resolve CIU_implies_CTX : core.

Lemma exists_CTX : exists R, IsCtxRel R.
Proof.
  exists CTX.
  apply CTX_IsCtxRel.
Qed.

Lemma CIU_beta_value : forall {Γ e2 v},
    EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
    (CIU_open Γ e2.[v/] (ELet v e2) /\ 
     CIU_open Γ (ELet v e2) e2.[v/]).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU.
  intuition idtac.
  1,5: apply -> subst_preserves_scope_exp; try eassumption;
    apply -> subst_preserves_scope_exp; eauto.
  1,3: simpl; do 2 constructor; [ constructor; apply -> subst_preserves_scope_val; eauto |
                             apply -> subst_preserves_scope_exp; eauto ].
  destruct H3 as [x D]. exists (S (S x)). simpl. apply term_let.
  pose proof (subst_preserves_scope_val v Γ). destruct H3.
  clear H4. specialize (H3 H0 0 ξ H1). constructor; auto.
  rewrite subst_comp, subst_extend_id.
  now rewrite subst_comp, scons_substcomp, substcomp_id_l in D.

  destruct H3 as [x D]. simpl in D. inv D.
  pose proof (subst_preserves_scope_val v Γ) as X. destruct X.
  clear H4. specialize (H3 H0 0 ξ H1).
  inv H7.
  rewrite subst_comp, subst_extend_id in H9.
  rewrite subst_comp, scons_substcomp, substcomp_id_l. eexists. exact H9.
Qed.

Lemma CTX_closed_under_substitution : forall {Γ e1 e2 v R},
    IsCtxRel R ->
    VAL Γ ⊢ v ->
    R (S Γ) e1 e2 ->
    R Γ e1.[v/] e2.[v/].
Proof.
  intros Γ e1 e2 v R HCtx Hscope_v HCtx_e1e2.
  destruct HCtx as [HCtx Hbiggest].
  destruct HCtx as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet [RLetRec [RPlus RIf]]]]]]]]].
  destruct (Rscope _ _ _ HCtx_e1e2) as [Hscope_e1 Hscope_e2].
  epose proof (@CIU_beta_value Γ e1 v Hscope_e1 _).
  epose proof (@CIU_beta_value Γ e2 v Hscope_e2 _).
  destruct H as [? _].
  destruct H0 as [_ ?].
  apply CIU_iff_Erel in H.
  apply CIU_iff_Erel in H0.
  apply Hbiggest in H; auto using Erel_IsPreCtxRel.
  apply Hbiggest in H0; auto using Erel_IsPreCtxRel.
  eapply Rtrans in H.
  eapply H.
  eapply Rtrans; revgoals.
  eapply H0.
  apply RLet.
  1-2: constructor; auto.
  1-2: auto.
  apply Rrefl. now constructor.
  auto.
Unshelve.
  1-2: auto.
Qed.

Theorem CIU_IsCtxRel : IsCtxRel CIU_open.
Proof.
  destruct exists_CTX as [R' HR'].
  eapply bigger_implies_IsCtxRel. 2: eauto using CIU_IsPreCtxRel. apply CTX_IsCtxRel.
  induction Γ; revgoals.
  - unfold CIU_open.
    intros.
    pose proof (H0 0 ltac:(lia)). break_match_hyp. 2: inversion H1.
    replace e1.[ξ] with e1.[v/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp. rewrite scons_substcomp_core.
      rewrite (closed_ignores_sub_val v); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    replace e2.[ξ] with e2.[v/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp. rewrite scons_substcomp_core.
      rewrite (closed_ignores_sub_val v); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    apply IHΓ.
    apply CTX_closed_under_substitution; auto; revgoals.
    + specialize (H0 0 ltac:(lia)).
      simpl. replace v with (v.ᵥ[idsubst]) by auto.
      apply -> subst_preserves_scope_val; eauto. intro. intros. inversion H2.
    + unfold subscoped.
      intros. apply H0. lia.
  - unfold CIU_open.
    intros.
    unfold CIU.
    intuition idtac.
    + apply -> subst_preserves_scope_exp; eauto. destruct HR'.
      eapply H1 with (e1:=e1) (e2:=e2). apply H2 in H; auto.
    + apply -> subst_preserves_scope_exp; eauto 3. destruct HR'.
      eapply H1 with (e1:=e1) (e2:=e2); eauto 3.
    + replace e1.[ξ] with e1 in H2; revgoals.
      { replace ξ with (upn 0 ξ) by auto.
        rewrite scoped_ignores_sub; auto. destruct HR'.
        eapply H3 with (e1:=e1) (e2:=e2); eauto.
      }
      replace e2.[ξ] with e2; revgoals.
      { replace ξ with (upn 0 ξ) by auto.
        rewrite scoped_ignores_sub; auto. destruct HR'.
        eapply H3 with (e1:=e1) (e2:=e2); eauto.
      }
      clear H0.
      generalize dependent e2. generalize dependent e1. generalize dependent F.
      induction F; intros.
      * destruct HR'. destruct H, H. apply (H4 CHole); auto. constructor.
      * inversion H1. subst.
        assert (EXPCLOSED e1) as EC1 by apply H.
        assert (EXPCLOSED e2) as EC2 by apply H.
        apply put_back in H2; auto. destruct H2. apply put_back_rev; auto.
        eapply IHF; auto. exists x. exact H0.
        destruct HR'. inversion H. clear H6.
        destruct a; inversion H4; subst.
        -- simpl. apply CTX_IsPreCtxRel; auto. apply forall_biforall_refl.
           apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H8.
           now apply H8.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           ++ apply Forall_app. split; auto.
              apply Forall_map. eapply Forall_impl. 2: exact H11.
              intros. now constructor.
           ++ apply Forall_app. split; auto.
              apply Forall_map. eapply Forall_impl. 2: exact H11.
              intros. now constructor.
           ++ apply CTX_refl. now constructor.
           ++ apply biforall_app. 2: constructor; auto.
              all: apply forall_biforall_refl; apply Forall_forall; 
                   intros; apply CTX_refl; rewrite Forall_forall in H11, H12.
              *** apply in_map_iff in H6 as [elem [? ?]]; subst.
                  apply H11 in H8. by constructor.
              *** by apply H12 in H6.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           1-2: now rewrite Nat.add_0_r. 1-2: apply CTX_refl; auto; now rewrite Nat.add_0_r.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           apply CTX_refl.
           all: apply scoped_val; auto.
        -- simpl. apply CTX_IsPreCtxRel; auto. apply forall_biforall_refl.
           apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H8.
           now apply H8.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           ++ apply Forall_app. split; auto.
              apply Forall_map. eapply Forall_impl. 2: exact H11.
              intros. now constructor.
           ++ apply Forall_app. split; auto.
              apply Forall_map. eapply Forall_impl. 2: exact H11.
              intros. now constructor.
           ++ apply CTX_refl. now constructor.
           ++ apply biforall_app. 2: constructor; auto.
              all: apply forall_biforall_refl; apply Forall_forall; 
                   intros; apply CTX_refl; rewrite Forall_forall in H11, H12.
              *** apply in_map_iff in H6 as [elem [? ?]]; subst.
                  apply H11 in H8. by constructor.
              *** by apply H12 in H6.
Qed.

Theorem Erel_IsCtxRel : IsCtxRel Erel_open.
Proof.
  unfold IsCtxRel.
  split.
  apply Erel_IsPreCtxRel.
  intros.
  apply CIU_iff_Erel.
  pose proof CIU_IsCtxRel.
  unfold IsCtxRel in H1.
  destruct H1.
  eapply H2; eauto.
Qed.

Corollary CTX_implies_CIU :
  forall e1 e2 Γ, CTX Γ e1 e2 -> CIU_open Γ e1 e2.
Proof.
  intros. eapply CIU_IsCtxRel. 2: exact H. auto.
Qed.

Global Hint Resolve CTX_implies_CIU : core.

Corollary CIU_iff_CTX :
  forall e1 e2 Γ, CTX Γ e1 e2 <-> CIU_open Γ e1 e2.
Proof.
  intros. split; auto.
Qed.

Corollary Erel_iff_CTX :
  forall e1 e2 Γ, CTX Γ e1 e2 <-> Erel_open Γ e1 e2.
Proof.
  intros. split; intros.
  * apply CIU_iff_Erel. auto.
  * apply CIU_iff_Erel in H. auto.
Qed.

Corollary CTX_eval : forall e1 v,
  EXPCLOSED e1 ->
  ⟨ [], e1 ⟩ -->* v -> CTX 0 e1 v /\ CTX 0 v e1.
Proof.
  intros. split; apply CIU_iff_CTX; intro; intros; simpl.
  rewrite closed_ignores_sub, closed_ignores_sub_val.
  4: rewrite closed_ignores_sub_val, closed_ignores_sub.
  1, 4: pose proof (CIU_eval _ _ H H0). all: auto. 1-2: apply H2.
  all: apply step_any_closedness in H0; auto; constructor.
Qed.

Lemma CIU_beta_values : forall {Γ e vl vals},
    VAL Γ ⊢ VFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> vl = length vals ->
    (CIU_open Γ (e.[list_subst (VFun vl e :: vals) idsubst]) (EApp (VFun vl e) (map VVal vals)) /\ 
     CIU_open Γ (EApp (VFun vl e) (map VVal vals)) (e.[list_subst (VFun vl e :: vals) idsubst])).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU. inversion H.
  intuition idtac.
  1,5: apply -> subst_preserves_scope_exp; try eassumption;
    apply -> subst_preserves_scope_exp; eauto.
  * replace (S vl + Γ) with (length (VFun vl e :: vals) + Γ).
    2: simpl; lia.
    eapply scoped_list_subscoped. constructor; auto.
    apply scope_idsubst.
  * replace (S vl + Γ) with (length (VFun vl e :: vals) + Γ).
    2: simpl; lia.
    eapply scoped_list_subscoped. constructor; auto.
    apply scope_idsubst.
  * simpl. constructor. constructor.
    - do 2 constructor.
      apply -> subst_preserves_scope_exp; eauto. do 2 rewrite Nat.add_succ_l.
      now apply up_scope, upn_scope.
    - intros. rewrite length_map in H6. rewrite indexed_to_forall in H0.
      replace (˝VLit 0%Z) with ((˝VLit 0%Z).[ξ]) by auto. rewrite map_nth.
      apply -> subst_preserves_scope_exp; eauto.
      rewrite map_nth. constructor.
      apply H0. by rewrite length_map in H6.
  * pose proof (full_eval_app_partial e.[upn (S vl) ξ] (map (subst_val ξ) vals) vl F
       ltac:(by rewrite length_map)).
    destruct H7 as [k D].
    exists (k + 2 + base.length (map (subst_val ξ) vals)). eapply term_step_term. simpl in *.
    rewrite map_map in *. simpl in *. exact H8. clear H8. 2: lia.
    rewrite subst_comp in *. rewrite subst_extend. rewrite subst_list_extend.
    2: by rewrite length_map. rewrite scons_substcomp_list in D.
    simpl in D. rewrite substcomp_id_l in D.
    by replace (k + 2 + base.length (map (subst_val ξ) vals) -
        S (S (base.length (map (subst_val ξ) vals)))) with k by lia.
  * simpl. do 2 constructor. do 2 constructor.
    apply -> subst_preserves_scope_exp; eauto. do 2 rewrite Nat.add_succ_l.
    now apply up_scope, upn_scope.
    intros. rewrite length_map in H6. rewrite indexed_to_forall in H0.
    replace (˝VLit 0%Z) with ((˝VLit 0%Z).[ξ]) by auto. rewrite map_nth.
    apply -> subst_preserves_scope_exp; eauto.
    rewrite map_nth. constructor. apply H0. by rewrite length_map in H6.
  * pose proof (full_eval_app_partial e.[upn (S vl) ξ] (map (subst_val ξ) vals) vl F
       ltac:(by rewrite length_map)).
    simpl in *. rewrite map_map in *.
    eapply terminates_step_any in H7. 2: exact H8. clear H8.
    rewrite subst_comp in *. rewrite subst_extend in H7. rewrite subst_list_extend in H7.
    2: by rewrite length_map. rewrite scons_substcomp. rewrite scons_substcomp_list.
    simpl. rewrite substcomp_id_l. assumption.
Qed.

Corollary CTX_beta_values : forall {Γ e vl vals},
    VAL Γ ⊢ VFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> vl = length vals ->
    (CTX Γ (e.[list_subst (VFun vl e :: vals) idsubst]) (EApp (VFun vl e) (map VVal vals)) /\ 
     CTX Γ (EApp (VFun vl e) (map VVal vals)) (e.[list_subst (VFun vl e :: vals) idsubst])).
Proof.
  intros. split; apply CIU_iff_CTX, CIU_beta_values; auto.
Qed.

Definition equivalent_exps (e1 e2 : Exp) (R : Exp -> Exp -> Prop) : Prop :=
  forall v1, ⟨ [], e1 ⟩ -->* v1 -> (exists v2, ⟨ [], e2 ⟩ -->* v2 /\ R v1 v2).

Fixpoint equivalent_values (n : nat) (v1 v2 : Exp) : Prop :=
match n with
| 0 => True
| S n' =>
  match v1, v2 with
  | VLit l1, VLit l2 => l1 = l2
  | VPid p1, VPid p2 => p1 = p2
  | VFun vl1 b1, VFun vl2 b2 => forall vals, Forall (fun v => VALCLOSED v) vals ->
    length vals = vl1 -> length vals = vl2 ->
    equivalent_exps (b1.[list_subst (VFun vl1 b1::vals) idsubst]) (b2.[list_subst (VFun vl2 b2::vals) idsubst]) (equivalent_values n')
  | VCons v1 v2, VCons v1' v2' => equivalent_values n' v1 v1' /\ equivalent_values n' v2 v2'
  | VNil, VNil => True
  | _, _ => False
  end
end.

Corollary CIU_iff_CIU_open v1 v2 :
  CIU v1 v2 <-> CIU_open 0 v1 v2.
Proof.
  split; intros.
  * intro. intros.
    rewrite closed_ignores_sub. rewrite closed_ignores_sub.
    auto. apply H. apply H.
  * unfold CIU_open in H.
    specialize (H idsubst (scope_idsubst 0)).
    now do 2 rewrite idsubst_is_id in H.
Qed.

Theorem CIU_vlist e1 e2:
  VALCLOSED e1 -> VALCLOSED e2 ->
  CIU (ECons e1 e2) (VCons e1 e2) /\ CIU (VCons e1 e2) (ECons e1 e2).
Proof.
  intros. split.
  * split. 2: split.
    - repeat constructor; auto.
    - repeat constructor; auto.
    - intros. destruct H2.
      inversion H2; subst.
      inversion H7; subst.
      inversion H8; subst. eexists. exact H9.
  * split. 2: split.
    - repeat constructor; auto.
    - repeat constructor; auto.
    - intros. destruct H2. exists (3 + x).
      repeat constructor; auto.
Qed.

Definition eq_exps (e1 e2 : Exp) := forall n, equivalent_exps e1 e2 (equivalent_values n).

Theorem equivalent_valexps :
  forall n e1 e2, VALCLOSED e1 -> VALCLOSED e2 ->
  equivalent_exps e1 e2 (equivalent_values n) -> equivalent_values n e1 e2.
Proof.
  induction n; intros; simpl; auto; destruct e1, e2; repeat destruct_scope; unfold equivalent_exps in *; try lia.
  * epose proof (H1 (VLit l) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. by auto.
  * epose proof (H1 (VLit l) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. by auto.
  * epose proof (H1 (VLit l) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * intros. epose proof (H1 (VFun vl e) _) as [v2 [Eval2 eq2]]. inversion Eval2.
    inversion H6. 2: { apply value_nostep in H7. contradiction. }
    subst. simpl in eq2. apply eq2; auto.
  * epose proof (H1 (VFun vl e) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) _) as [v2 [Eval2 eq2]]. inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) _) as [v2 [Eval2 eq2]]. inversion Eval2.
    inversion H. subst. 2: { inversion H0. } simpl in eq2. destruct eq2.
    assert ((forall v1 : Val,
       ⟨ [], e1_1 ⟩ -->* v1 -> exists v2 : Val, ⟨ [], e2_1 ⟩ -->* v2 /\ equivalent_values n v1 v2)).
    {
      intros. destruct H7 as [k E1]. inversion E1; subst.
      2: { apply value_nostep in H7. contradiction. }
      exists e2_1. split; auto. exists 0. constructor.
    }
    assert ((forall v1 : Val,
       ⟨ [], e1_2 ⟩ -->* v1 -> exists v2 : Val, ⟨ [], e2_2 ⟩ -->* v2 /\ equivalent_values n v1 v2)).
    {
      intros. destruct H8 as [k E1]. inversion E1; subst.
      2: { apply value_nostep in H8. contradiction. }
      exists e2_2. split; auto. exists 0. constructor.
    }
    apply IHn in H7. apply IHn in H8. all: auto.
  Unshelve.
   all: exists 0; constructor.
Qed.

Theorem terminating_implies_equivalence_helper :
  forall e1 e2 (P : CTX 0 e2 e1), CTX 0 e1 e2 -> eq_exps e1 e2.
Proof.
  intros. intro. revert H. generalize dependent e2. generalize dependent e1.
  induction n; intros.
  * unfold equivalent_exps. intros. cbn. destruct H, H.
    apply ex_intro in H0. apply -> terminates_eq_terminates_sem in H0.
    apply (H1 CHole ltac:(constructor)) in H0. apply terminates_eq_terminates_sem in H0.
    destruct H0. exists x. split; auto.
  * unfold equivalent_exps. intros. cbn. assert (CTX 0 e1 e2) as P' by auto.
    destruct H as [[Hscope1 Hscope2] He1e2].
    apply ex_intro in H0 as H0'. apply -> terminates_eq_terminates_sem in H0'.
    pose proof (He1e2 CHole ltac:(constructor) H0'). simpl in H.
    apply terminates_eq_terminates_sem in H. destruct H as [x HD].
    exists x. split; auto.
    clear H0'.
    generalize dependent x.
    destruct v1; intros; try lia.
    - destruct x; try lia.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        ** break_match_hyp. now apply lit_eqb_eq in Heqb. congruence.
        ** apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X. 
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X. 
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
    - destruct x; try lia.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        ** case_match. 2: congruence. inv H2.
           by apply Nat.eqb_eq in H.
        ** apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
    - apply step_any_closedness in H0. inv H0. lia. constructor. assumption.
    - destruct x; try lia.
      + apply ex_intro in H0 as D.
        apply -> terminates_eq_terminates_sem in D.
        destruct P as [HS He2e1].
        epose proof (He2e1 (CCase1 CHole (PLit l) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct H0 as [ke1 HD1]. eapply frame_indep_nil in HD1.
        eapply terminates_step_any_2 in H6. 2: exact HD1.
        inv H6; simpl in *.
        apply inf_diverges in H7. contradiction.
      + apply ex_intro in H0 as D.
        apply -> terminates_eq_terminates_sem in D.
        destruct P as [HS He2e1].
        epose proof (He2e1 (CCase1 CHole (PPid p) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct H0 as [ke1 HD1]. eapply frame_indep_nil in HD1.
        eapply terminates_step_any_2 in H6. 2: exact HD1.
        inv H6; simpl in *.
        apply inf_diverges in H7. contradiction.
      + apply step_any_closedness in HD. inv HD. lia. constructor. assumption.
      + intros. apply IHn.
        -- 
        assert (CTX 0 e1 e2). {
          split. split. all: auto.
        }
        assert (CTX 0 (VFun vl0 e0) (VFun vl e)). {
          apply CTX_eval in H0; auto. apply CTX_eval in HD; auto.
          assert (Transitive (CTX 0)). { apply CTX_IsPreCtxRel. }
          destruct H0 as [HH1 HH2], HD as [HH3 HH4].
          epose proof (H4 _ _ _ HH4 P) as T.
          epose proof (H4 _ _ _ T HH1). auto.
        }
        epose proof CTX_IsPreCtxRel as X. destruct X as [_ [_ [_ [Rtrans [_ [RApp _]]]]]].
        unfold CompatibleApp in RApp.
        assert (VALCLOSED (VFun vl e)). {
          apply step_any_closedness in H0. now inversion H0. constructor. auto.
        }
        assert (VALCLOSED (VFun vl0 e0)). {
          apply step_any_closedness in HD. now inversion HD. constructor. auto.
        }
        apply RApp with (vals1 := map VVal vals)
            (vals2 := map VVal vals) in H4; auto.
        ** epose proof (CTX_beta_values H5 H (eq_sym H1)) as [CTX1 CTX2].
           epose proof (CTX_beta_values H6 H (eq_sym H2)) as [CTX3 CTX4].
           epose proof (Rtrans 0 _ _ _ CTX3 H4) as T.
           epose proof (Rtrans 0 _ _ _ T CTX2) as T'. assumption.
        ** eapply Forall_map, Forall_impl. 2: exact H.
           intros. now constructor.
        ** eapply Forall_map, Forall_impl. 2: exact H.
           intros. now constructor.
        ** apply forall_biforall_refl. apply Forall_map, Forall_forall.
           intros. apply CTX_refl. constructor.
           rewrite Forall_forall in H. by auto.
        --
        assert (CTX 0 e1 e2). {
          split. split. all: auto.
        }
        assert (CTX 0 (VFun vl e) (VFun vl0 e0)). {
          apply CTX_eval in H0; auto. apply CTX_eval in HD; auto.
          assert (Transitive (CTX 0)). { apply CTX_IsPreCtxRel. }
          destruct H0 as [HH1 HH2], HD as [HH3 HH4].
          epose proof (H4 _ _ _ HH2 P') as T.
          epose proof (H4 _ _ _ T HH3). auto.
        }
        epose proof CTX_IsPreCtxRel as X. destruct X as [_ [_ [_ [Rtrans [_ [RApp _]]]]]].
        unfold CompatibleApp in RApp.
        assert (VALCLOSED (VFun vl e)). {
          apply step_any_closedness in H0. now inversion H0. constructor. auto.
        }
        assert (VALCLOSED (VFun vl0 e0)). {
          apply step_any_closedness in HD. now inversion HD. constructor. auto.
        }
        apply RApp with (vals1 := map VVal vals)
            (vals2 := map VVal vals) in H4; auto.
        ** epose proof (CTX_beta_values H5 H (eq_sym H1)) as [CTX1 CTX2].
           epose proof (CTX_beta_values H6 H (eq_sym H2)) as [CTX3 CTX4].
           epose proof (Rtrans 0 _ _ _ CTX1 H4) as T.
           epose proof (Rtrans 0 _ _ _ T CTX4) as T'. assumption.
        ** eapply Forall_map, Forall_impl. 2: exact H.
           intros. now constructor.
        ** eapply Forall_map, Forall_impl. 2: exact H.
           intros. now constructor.
        ** apply forall_biforall_refl. apply Forall_map, Forall_forall.
           intros. apply CTX_refl. constructor.
           rewrite Forall_forall in H. by auto.
      + apply ex_intro in H0 as D.
        apply -> terminates_eq_terminates_sem in D.
        destruct P as [HS He2e1].
        epose proof (He2e1 (CCase1 CHole (PNil) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct H0 as [ke1 HD1]. eapply frame_indep_nil in HD1.
        eapply terminates_step_any_2 in H6. 2: exact HD1.
        inv H6; simpl in *.
        apply inf_diverges in H7. contradiction.
      + apply ex_intro in H0 as D.
        apply -> terminates_eq_terminates_sem in D.
        destruct P as [HS He2e1].
        epose proof (He2e1 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct H0 as [ke1 HD1]. eapply frame_indep_nil in HD1.
        eapply terminates_step_any_2 in H6. 2: exact HD1.
        inv H6; simpl in *.
        apply inf_diverges in H7. contradiction.
    - destruct x; try lia.
      + epose proof (He1e2 (CCase1 CHole PNil (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole PNil (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole PNil (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole PNil (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole PNil (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
    - destruct x; try lia.
      + epose proof (He1e2 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + epose proof (He1e2 (CCase1 CHole (PCons PVar PVar) (VLit 0%Z) inf) _ _) as X.
        simpl in X. destruct X as [k X]. inv X.
        destruct HD as [ke2 HD2]. eapply frame_indep_nil in HD2.
        eapply terminates_step_any_2 in H6. 2: exact HD2.
        inv H6; simpl in *.
        apply inf_diverges in H8. contradiction.
      + apply CIU_eval in H0 as [E1_1 E1_2].
        apply CIU_eval in HD as [E2_1 E2_2].
        all: auto.
        assert (VALCLOSED v1_1 /\ VALCLOSED v1_2
             /\ VALCLOSED x1 /\ VALCLOSED x2) as [V1 [V2 [V3 V4]]]. {
          apply CIU_closed in E1_1 as [_ E].
          apply CIU_closed in E2_1 as [_ F].
          clear -E F. by repeat destruct_scope.
        }
        epose proof (CIU_vlist _ _ V1 V2) as [P1 P2].
        epose proof (CIU_vlist _ _ V3 V4) as [P3 P4].
        apply CIU_iff_CIU_open in P1. apply CIU_iff_CIU_open in P2.
        apply CIU_iff_CIU_open in P3. apply CIU_iff_CIU_open in P4.
        apply CIU_iff_CIU_open in E1_1. apply CIU_iff_CIU_open in E1_2.
        apply CIU_iff_CIU_open in E2_1. apply CIU_iff_CIU_open in E2_2.
        assert (CIU_open 0 (ECons v1_1 v1_2) (ECons x1 x2)) as J1. {
          epose proof (CIU_IsPreCtxRel) as [? [? [? [T ?]]]].
          eapply T. apply P1.
          eapply T. apply E1_2.
          eapply T. apply CIU_iff_CTX. exact P'. auto.
          eapply T. apply E2_1. auto.
        }
        assert (CIU_open 0 (ECons x1 x2) (ECons v1_1 v1_2)) as J2. {
          epose proof (CIU_IsPreCtxRel) as [? [? [? [T ?]]]].
          eapply T. apply P3.
          eapply T. apply E2_2.
          eapply T. apply CIU_iff_CTX. exact P.
          eapply T. apply E1_1. auto.
        }
        apply CIU_iff_CIU_open in J1. apply CIU_iff_CIU_open in J2.
        apply CIU_list_parts in J1 as [J1_1 J1_2]. apply CIU_list_parts in J2 as [J2_1 J2_2].
        all: auto.
        apply CIU_iff_CIU_open in J1_1. apply CIU_iff_CIU_open in J1_2.
        apply CIU_iff_CIU_open in J2_1. apply CIU_iff_CIU_open in J2_2.
        apply CIU_iff_CTX in J1_1. apply CIU_iff_CTX in J1_2.
        apply CIU_iff_CTX in J2_1. apply CIU_iff_CTX in J2_2.
        eapply IHn in J1_1. eapply IHn in J1_2. all: auto.
        apply equivalent_valexps in J1_1. apply equivalent_valexps in J1_2.
        all: auto.
Unshelve. (** TODO This is boiler plate basically... *)
  all: try by repeat constructor; simpl; lia. (* solves scopes *)
  all: try (simpl; destruct H0 as [x DD]; exists (2 + x); constructor;
            eapply term_step_term;
              [eapply frame_indep_nil in DD; exact DD
              | replace (S x - x) with 1 by lia; eapply term_case_true;
                [cbn; try rewrite Nat.eqb_refl; try rewrite lit_eqb_refl; reflexivity
                |constructor]
              | lia]). (* e1-based reductions *)
  all: try (simpl; destruct HD as [x DD]; exists (2 + x); constructor;
            eapply term_step_term;
              [eapply frame_indep_nil in DD; exact DD
              | replace (S x - x) with 1 by lia; eapply term_case_true;
                [cbn; try rewrite Nat.eqb_refl; try rewrite lit_eqb_refl; reflexivity
                |constructor]
              | lia]). (* e2-based reductions *)
Qed.

(** MAJOR RESULT: *)
Theorem terminating_implies_equivalence :
  forall e1 e2, CTX 0 e2 e1 -> CTX 0 e1 e2 -> eq_exps e1 e2 /\ eq_exps e2 e1.
Proof.
  intros. split; eapply terminating_implies_equivalence_helper; auto.
Qed.

Definition equivalent_exps2 (e1 e2 : Exp) (R : Exp -> Exp -> Prop) : Prop :=
  forall v1 Fs, FSCLOSED Fs -> ⟨ Fs, e1 ⟩ -->* v1 -> (exists v2, ⟨ Fs, e2 ⟩ -->* v2 /\ R v1 v2).

Fixpoint equivalent_values2 (n : nat) (v1 v2 : Exp) : Prop :=
match n with
| 0 => True
| S n' =>
  match v1, v2 with
  | VLit l1, VLit l2 => l1 = l2
  | VPid p1, VPid p2 => p1 = p2
  | VFun vl1 b1, VFun vl2 b2 => forall vals, Forall (fun v => VALCLOSED v) vals ->
    length vals = vl1 -> length vals = vl2 ->
    equivalent_exps2 (b1.[list_subst (VFun vl1 b1::vals) idsubst]) (b2.[list_subst (VFun vl2 b2::vals) idsubst]) (equivalent_values2 n')
  | VCons v1 v2, VCons v1' v2' => equivalent_values2 n' v1 v1' /\ equivalent_values2 n' v2 v2'
  | VNil, VNil => True
  | _, _ => False
  end
end.

Theorem equivalent_values2_downclosed :
  forall n,
    (forall v1 v2, equivalent_values2 (S n) v1 v2 -> equivalent_values2 n v1 v2).
Proof.
  induction n; intros; auto; destruct v1, v2; simpl; trivial.
  destruct v, v0; simpl; trivial.
  * intros. intro. intros. specialize (H vals H0 H1 H2).
    apply H in H4 as [v2' [Cl ?]]; auto.
    exists v2'; split. auto. apply IHn. auto.
  * destruct H. apply IHn in H. apply IHn in H0. auto.
Qed.

Definition eq_exps2 (e1 e2 : Exp) :=
  equivalent_exps2 e1 e2 (fun v1 v2 => forall n, equivalent_values2 n v1 v2).

Theorem equivalent2_valexps :
  forall n e1 e2, VALCLOSED e1 -> VALCLOSED e2 ->
  equivalent_exps2 e1 e2 (equivalent_values2 n) -> equivalent_values2 n e1 e2.
Proof.
  induction n; intros; simpl; auto; destruct e1, e2; unfold equivalent_exps in *; repeat destruct_scope; try lia.
  * epose proof (H1 (VLit l) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VLit l) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VPid p) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * intros. epose proof (H1 (VFun vl e) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H5.
    2: { apply value_nostep in H6. contradiction. }
    subst. simpl in eq2. apply eq2; auto.
  * epose proof (H1 (VFun vl e) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VFun vl e) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 VNil [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * epose proof (H1 (VCons e1_1 e1_2) [] ltac:(constructor) _) as [v2 [Eval2 eq2]].
    inversion Eval2. inversion H.
    subst. 2: inversion H0. auto.
  * split; apply IHn; auto; unfold equivalent_exps2 in *; intros.
    - assert (FSCLOSED (FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z) :: Fs)). {
        constructor. constructor. do 2 constructor. all: simpl; auto.
      }
      destruct H0 as [x D].
      assert (⟨ FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z) :: Fs, VCons e1_1 e1_2 ⟩ -->* v1). {
        exists (S x).
        econstructor. constructor. constructor; auto.
        simpl. assumption.
      }
      specialize (H1 v1 (FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z) :: Fs) H2 H0)
          as [v2 [[k2 E2] Eq]].
      inversion E2; subst; inv H1.
      simpl in H15. inv H15. simpl in H7.
      exists v2. split; auto. now exists k.
      now apply equivalent_values2_downclosed.
    - assert (FSCLOSED (FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z) :: Fs)). {
        constructor. constructor. do 2 constructor. all: simpl; auto.
      }
      destruct H0 as [x D].
      assert (⟨ FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z) :: Fs, VCons e1_1 e1_2 ⟩ -->* v1). {
        exists (S x).
        econstructor. constructor. constructor; auto.
        simpl. assumption.
      }
      specialize (H1 v1 (FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z) :: Fs) H2 H0)
          as [v2 [[k2 E2] Eq]].
      inversion E2; inv H1; subst.
      simpl in H20. inv H20. simpl in H7.
      exists v2. split; auto. now exists k.
      now apply equivalent_values2_downclosed.
  Unshelve.
   all: exists 0; constructor.
Qed.

Theorem equivalence_implies_terminating2 :
  forall e1 e2, EXPCLOSED e1 -> EXPCLOSED e2 -> eq_exps2 e1 e2 -> eq_exps2 e2 e1 ->
    (CIU e1 e2 /\ CIU e2 e1).
Proof.
  intros. unfold CIU, eq_exps2, equivalent_exps2 in *.
  repeat split; auto; intros.
  * apply terminates_eq_terminates_sem in H4 as [v H4]. apply H1 in H4.
    destruct H4, H4. apply terminates_eq_terminates_sem. exists x; auto. auto.
  * apply terminates_eq_terminates_sem in H4 as [v H4]. apply H2 in H4.
    destruct H4, H4. apply terminates_eq_terminates_sem. exists x; auto. auto.
Qed.

Theorem terminating_implies_equivalence_helper2 :
  forall e1 e2 (P : CIU e2 e1), CIU e1 e2 -> eq_exps2 e1 e2.
Proof.
  intros. intro. intros.
  destruct P, H, H3, H4.
  apply ex_intro in H1 as H1'. apply terminates_eq_terminates_sem in H1'.
  epose proof (H6 _ H0 H1').
  apply terminates_eq_terminates_sem in H7. clear H1'. destruct H7.
  exists x; split; auto. intro.
  generalize dependent v1. generalize dependent x. generalize dependent Fs.
  induction n; intros.
  * simpl. auto.
  * simpl.
    assert (VALCLOSED v1) as Vv1 by by apply step_any_closedness in H1.
    assert (VALCLOSED x) as Vx by by apply step_any_closedness in H7.
    destruct H1 as [k1 D1].
    destruct H7 as [k2 D2].
    destruct v1, x; repeat destruct_scope; try lia.
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩) as X.
        {
          econstructor. constructor. cbn. rewrite lit_eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA as [k D].
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in D. 2: eauto.
      inv D. simpl in *. break_match_hyp. 2: congruence.
      inv H8. now apply lit_eqb_eq in Heqb.
      apply inf_diverges in H13. contradiction.
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩) as X.
        {
          econstructor. constructor. cbn. rewrite lit_eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA as [k D].
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in D. 2: eauto.
      inv D. simpl in *.
      apply inf_diverges in H13. contradiction.
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩) as X.
        {
          econstructor. constructor. cbn. rewrite lit_eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA as [k D].
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in D. 2: eauto.
      inv D. simpl in *.
      apply inf_diverges in H14. contradiction.
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩) as X.
        {
          econstructor. constructor. cbn. rewrite lit_eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA as [k D].
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in D. 2: eauto.
      inv D. simpl in *.
      apply inf_diverges in H13. contradiction.
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩) as X.
        {
          econstructor. constructor. cbn. rewrite lit_eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA as [k D].
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in D. 2: eauto.
      inv D. simpl in *.
      apply inf_diverges in H15. contradiction.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e2 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. rewrite lit_eqb_refl.
          reflexivity. constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k2 + 1). eapply transitive_eval. exact D2. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H14.
    - assert (| Fs ++ [FCase (PPid p) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PPid p) (VLit 0%Z) inf], VPid p ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. cbn. rewrite Nat.eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PPid p) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. subst. simpl in *. break_match_hyp. 2: congruence.
      inv H9. now apply Nat.eqb_eq in Heqb.
      subst. apply inf_diverges in H14. contradiction.
    - assert (| Fs ++ [FCase (PPid p) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PPid p) (VLit 0%Z) inf], VPid p ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. cbn. rewrite Nat.eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PPid p) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. subst. simpl in *.
      subst. apply inf_diverges in H15. contradiction.
    - assert (| Fs ++ [FCase (PPid p) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PPid p) (VLit 0%Z) inf], VPid p ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. cbn. rewrite Nat.eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PPid p) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. subst. simpl in *.
      subst. apply inf_diverges in H14. contradiction.
    - assert (| Fs ++ [FCase (PPid p) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PPid p) (VLit 0%Z) inf], VPid p ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. rewrite Nat.eqb_refl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PPid p) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H16.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FCase (PLit l) (VLit 0%Z) inf], e2 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D2.
        assert (⟨ [FCase (PLit l) (VLit 0%Z) inf], VLit l ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. rewrite lit_eqb_refl.
          reflexivity. constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k2 + 1). eapply transitive_eval. exact D2. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FCase (PLit l) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PLit l) (VLit 0%Z) inf]) in D1.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H15.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FCase (PPid p) (VLit 0%Z) inf], e2 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D2.
        assert (⟨ [FCase (PPid p) (VLit 0%Z) inf], (VPid p) ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. rewrite Nat.eqb_refl.
          reflexivity. constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k2 + 1). eapply transitive_eval. exact D2. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FCase (PPid p) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PPid p) (VLit 0%Z) inf]) in D1.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H15.
    - intros. unfold equivalent_exps2. intros.
      assert (⟨ Fs ++ [FApp1 (map VVal vals)] ++ Fs0, e1 ⟩ -->* v1) as T1'. {
        apply frame_indep_nil with (Fs' := [FApp1 (map VVal vals)] ++ Fs0) in D1.

        assert (exists k, ⟨ [FApp1 (map VVal vals)] ++ Fs0, VFun vl e ⟩ -[k]->
                ⟨Fs0, e.[VFun vl e .: list_subst vals idsubst]⟩) as X. {
          apply app1_eval; auto.
        }
        destruct X as [k X].
        epose proof (transitive_eval _ _ _ _ _ D1 _ _ _ X) as HD2.
        destruct H12 as [l D].
        epose proof (transitive_eval _ _ _ _ _ HD2 _ _ _ D).
        by eexists; eauto.
      }
      eapply ex_intro in T1' as T1.
      apply terminates_eq_terminates_sem in T1.
      epose proof (H6 (Fs ++ ([FApp1 (map VVal vals)] ++ Fs0)) _ T1) as X.

      destruct X as [k D].
      apply frame_indep_nil with (Fs' := [FApp1 (map VVal vals)] ++ Fs0) in D2.
      assert (exists k, ⟨ [FApp1 (map VVal vals)] ++ Fs0, VFun vl0 e0 ⟩ -[k]->
                ⟨Fs0, e0.[VFun vl0 e0 .: list_subst vals idsubst]⟩) as X. {
        apply app1_eval; auto.
      }
      destruct X as [l Dl].
      eapply terminates_step_any_2 in D. 2: exact D2.
      eapply terminates_step_any_2 in D. 2: exact Dl.
      apply terminates_in_k_eq_terminates_in_k_sem in D. destruct D as [vfin D].
      exists vfin. split.
      + eexists. eassumption.
      + eapply IHn.
        3: { exact T1'. }
        ** apply Forall_app. split. 2: apply Forall_app; split.
           all: auto. do 2 constructor. eapply Forall_map, Forall_impl.
             intros. apply scoped_val. 2: exact H1.
             assumption.
        ** epose proof (transitive_eval _ _ _ _ _ D2 _ _ _ Dl) as X.
           epose proof (transitive_eval _ _ _ _ _ X _ _ _ D).
           by eexists; eauto.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FCase (PNil) (VLit 0%Z) inf], e2 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PNil) (VLit 0%Z) inf]) in D2.
        assert (⟨ [FCase (PNil) (VLit 0%Z) inf], VNil ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity. constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k2 + 1). eapply transitive_eval. exact D2. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FCase (PNil) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PNil) (VLit 0%Z) inf]) in D1.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H15.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf], e2 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase ((PCons PVar PVar)) (VLit 0%Z) inf]) in D2.
        assert (⟨ [FCase ((PCons PVar PVar)) (VLit 0%Z) inf], VCons x1 x2 ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity. constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k2 + 1). eapply transitive_eval. exact D2. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FCase ((PCons PVar PVar)) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase ((PCons PVar PVar)) (VLit 0%Z) inf]) in D1.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H17.
    - assert (| Fs ++ [FCase (PNil) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PNil) (VLit 0%Z) inf], VNil ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase PNil (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H14.
    - assert (| Fs ++ [FCase (PNil) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PNil) (VLit 0%Z) inf], VNil ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase PNil (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H14.
    - assert (| Fs ++ [FCase (PNil) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PNil) (VLit 0%Z) inf], VNil ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase PNil (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H15.
    - assert (| Fs ++ [FCase (PNil) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PNil) (VLit 0%Z) inf], VNil ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase PNil (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase PNil (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H16.
    - assert (| Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PCons PVar PVar) (VLit 0%Z) inf], (VCons v1_1 v1_2) ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H16.
    - assert (| Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PCons PVar PVar) (VLit 0%Z) inf], (VCons v1_1 v1_2) ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H16.
    - assert (| Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PCons PVar PVar) (VLit 0%Z) inf], (VCons v1_1 v1_2) ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H17.
    - assert (| Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf], e1 | ↓) as T1. {
        apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D1.
        assert (⟨ [FCase (PCons PVar PVar) (VLit 0%Z) inf], (VCons v1_1 v1_2) ⟩ -[1]-> ⟨[], VLit 0%Z⟩).
        {
          econstructor. constructor. simpl. reflexivity.
          constructor.
        }
        apply terminates_eq_terminates_sem. exists (VLit 0%Z).
        exists (k1 + 1). eapply transitive_eval. exact D1. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FCase (PCons PVar PVar) (VLit 0%Z) inf]) _ T1).
      destruct CONTRA.
      apply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VLit 0%Z) inf]) in D2.
      eapply terminates_step_any_2 in H1. 2: eauto.
      inv H1. now apply inf_diverges in H16.
    - assert (FSCLOSED (Fs ++ [FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z)])) as Hcl1. {
          apply Forall_app. split. auto.
          do 2 constructor. all: simpl; auto.
      }
      assert (FSCLOSED (Fs ++ [FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z)])) as Hcl2. {
          apply Forall_app. split. auto.
          do 2 constructor. all: simpl; auto.
      }
      assert (⟨ Fs ++ [FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z)], e1 ⟩ -->* v1_1) as De1Pvar0. {
        exists (k1 + 1). eapply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z)]) in D1.
        eapply transitive_eval. exact D1. econstructor. constructor.
        constructor; auto. constructor.
      }
      assert (⟨ Fs ++ [FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z)], e2 ⟩ -->* x1) as De2Pvar0. {
        exists (k2 + 1). eapply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VVar 0) (VLit 0%Z)]) in D2.
        eapply transitive_eval. exact D2. econstructor. constructor.
        constructor; auto. constructor.
      }
      assert (⟨ Fs ++ [FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z)], e1 ⟩ -->* v1_2) as De1Pvar1. {
        exists (k1 + 1). eapply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z)]) in D1.
        eapply transitive_eval. exact D1. econstructor. constructor.
        constructor; auto. constructor.
      }
      assert (⟨ Fs ++ [FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z)], e2 ⟩ -->* x2) as De2Pvar1. {
        exists (k2 + 1). eapply frame_indep_nil with (Fs' := [FCase (PCons PVar PVar) (VVar 1) (VLit 0%Z)]) in D2.
        eapply transitive_eval. exact D2. econstructor. constructor.
        constructor; auto. constructor.
      }
      apply (IHn _ Hcl1 _ De2Pvar0) in De1Pvar0.
      apply (IHn _ Hcl2 _ De2Pvar1) in De1Pvar1.
      auto.
  Unshelve.
    all: try apply Forall_app; split; auto; simpl; constructor; auto.
    all: repeat constructor.
    all: simpl in *; try lia.
    eapply Forall_map, Forall_impl. 2: exact H1. intros. now apply scoped_val.
Qed.

Notation "e1 ≈[ Γ ]≈ e2" := (CTX Γ e1 e2 /\ CTX Γ e2 e1) (at level 70).
Notation "e1 ≈ e2" := (CTX 0 e1 e2 /\ CTX 0 e2 e1) (at level 70).

