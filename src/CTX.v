Require Export CIU.

Import ListNotations.

Definition Adequate (R : nat -> Exp -> Exp -> Prop) :=
  forall e1 e2, R 0 e1 e2 -> |[], e1| ↓ -> |[], e2| ↓.

Definition IsReflexive (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e,
  EXP Γ ⊢ e -> R Γ e e.

Definition CompatibleFun (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ vl vl' e1 e2, length vl = length vl' ->
    R (S (length vl) + Γ) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl' e2).

Definition CompatibleApp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f1 f2 vals1 vals2,
  Forall (fun e => EXP Γ ⊢ e) vals1 -> Forall (fun e => EXP Γ ⊢ e) vals2 ->
  EXP Γ ⊢ f1 -> EXP Γ ⊢ f2 ->
  R Γ f1 f2 -> 
  list_biforall (fun e1 e2 => R Γ e1 e2) vals1 vals2 ->
  R Γ (EApp f1 vals1) (EApp f2 vals2).

Definition CompatibleLet (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' x y e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP (S Γ) ⊢ e2 -> EXP (S Γ) ⊢ e2' ->
  R Γ e1 e1' -> R (S Γ) e2 e2' ->
  R Γ (ELet x e1 e2) (ELet y e1' e2').

Definition CompatibleLetRec (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f f' vl vl' b1 b1' e2 e2', length vl = length vl' ->
  EXP S (length vl) + Γ ⊢ b1 -> EXP S (length vl) + Γ ⊢ b1' -> 
  EXP S Γ ⊢ e2 -> EXP S Γ ⊢ e2' ->
  R (S (length vl) + Γ) b1 b1' -> R (S Γ) e2 e2' ->
  R Γ (ELetRec f vl b1 e2) (ELetRec f' vl' b1' e2').

Definition CompatiblePlus (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
  R Γ e1 e1' -> R Γ e2 e2' ->
  R Γ (EPlus e1 e2) (EPlus e1' e2').

Definition CompatibleIf (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2' e3 e3',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' -> EXP Γ ⊢ e3 -> EXP Γ ⊢ e3' ->
  R Γ e1 e1' -> R Γ e2 e2' -> R Γ e3 e3' ->
  R Γ (EIf e1 e2 e3) (EIf e1' e2' e3').

Definition IsPreCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  (forall Γ e1 e2, R Γ e1 e2 -> EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\ CompatibleApp R /\ CompatibleLet R/\ CompatibleLetRec R /\
  CompatiblePlus R /\ CompatibleIf R.

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
  * unfold CompatibleLetRec.
    intros. now apply Erel_LetRec_compat.
  * unfold CompatiblePlus.
    intros. now apply Erel_Plus_compat.
  * unfold CompatibleIf.
    intros. now apply Erel_If_compat.
Qed.

Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open.
Proof.
  pose proof Erel_IsPreCtxRel.
  unfold IsPreCtxRel in *.
  intuition idtac.
  all: unfold Adequate, Transitive, IsReflexive, CompatibleFun,
    CompatibleApp, CompatibleLet, CompatibleLetRec, CompatiblePlus, CompatibleIf; intros.
  all: try apply CIU_iff_Erel.
  * apply CIU_iff_Erel in H8.
    apply H0 in H8.
    intuition.
  * apply CIU_iff_Erel in H8.
    apply H0 in H8.
    intuition.
  * apply CIU_iff_Erel in H8.
    apply H in H8. auto.
  * now apply H1.
  * apply CIU_iff_Erel in H8.
    apply CIU_iff_Erel in H10.
    eapply H2; eauto.
  * apply CIU_iff_Erel in H10.
    now eapply H3.
  * apply CIU_iff_Erel in H13.
    eapply biforall_impl in H14.
    eapply H4; eauto.
    intros. now apply CIU_iff_Erel.
  * apply CIU_iff_Erel in H13.
    apply CIU_iff_Erel in H14.
    now eapply H5.
  * apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    now eapply H6.
  * apply CIU_iff_Erel in H13.
    apply CIU_iff_Erel in H14.
    now apply H7.
  * apply CIU_iff_Erel in H15.
    apply CIU_iff_Erel in H16.
    apply CIU_iff_Erel in H17.
    eapply H9; eauto.
Qed.

Inductive Ctx :=
| CHole
| CFun      (vl : list Var) (e : Ctx)
| CAppFun   (exp : Ctx) (l : list Exp)
| CAppParam (exp : Exp) (l1 : list Exp) (c : Ctx) (l2 : list Exp)  (** one of the middle ones is a ctx *)
| CLet1     (v : Var) (e1 : Ctx) (e2 : Exp)
| CLet2     (v : Var) (e1 : Exp) (e2 : Ctx)
| CLetRec1  (f : FunctionIdentifier) (vl : list Var) (b : Ctx) (e : Exp)
| CLetRec2  (f : FunctionIdentifier) (vl : list Var) (b : Exp) (e : Ctx)
| CPlus1     (e1 : Ctx) (e2 : Exp)
| CPlus2     (e1 : Exp) (e2 : Ctx)
| CIf1      (e1 : Ctx) (e2 e3 : Exp)
| CIf2      (e1 : Exp) (e2 : Ctx) (e3 : Exp)
| CIf3      (e1 e2 : Exp) (e3 : Ctx).

Fixpoint plug (C : Ctx) (p : Exp) :=
match C with
| CHole => p
| CFun vl e => EFun vl (plug e p)
| CAppFun exp l => EApp (plug exp p) l
| CAppParam exp l1 c l2 => EApp exp (l1 ++ [plug c p] ++ l2)
| CLet1 v e1 e2 => ELet v (plug e1 p) e2
| CLet2 v e1 e2 => ELet v e1 (plug e2 p)
| CLetRec1 f vl b e => ELetRec f vl (plug b p) e
| CLetRec2 f vl b e => ELetRec f vl b (plug e p)
| CPlus1 e1 e2 => EPlus (plug e1 p) e2
| CPlus2 e1 e2 => EPlus e1 (plug e2 p)
| CIf1 e1 e2 e3 => EIf (plug e1 p) e2 e3
| CIf2 e1 e2 e3 => EIf e1 (plug e2 p) e3
| CIf3 e1 e2 e3 => EIf e1 e2 (plug e3 p)
end.

Fixpoint plugc (Where : Ctx) (p : Ctx) :=
match Where with
| CHole => p
| CFun vl e => CFun vl (plugc e p)
| CAppFun exp l => CAppFun (plugc exp p) l
| CAppParam exp l1 c l2 => CAppParam exp l1 (plugc c p) l2
| CLet1 v e1 e2 => CLet1 v (plugc e1 p) e2
| CLet2 v e1 e2 => CLet2 v e1 (plugc e2 p)
| CLetRec1 f vl b e => CLetRec1 f vl (plugc b p) e
| CLetRec2 f vl b e => CLetRec2 f vl b (plugc e p)
| CPlus1 e1 e2 => CPlus1 (plugc e1 p) e2
| CPlus2 e1 e2 => CPlus2 e1 (plugc e2 p)
| CIf1 e1 e2 e3 => CIf1 (plugc e1 p) e2 e3
| CIf2 e1 e2 e3 => CIf2 e1 (plugc e2 p) e3
| CIf3 e1 e2 e3 => CIf3 e1 e2 (plugc e3 p)
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
| CEScope_Let1 : forall Γ x C e2,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP (S Γ) ⊢ e2 ->
    EECTX Γh ⊢ CLet1 x C e2 ∷ Γ
| CEScope_Let2 : forall Γ x e1 C,
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ C ∷ (S Γ) ->
    EECTX Γh ⊢ CLet2 x e1 C ∷ Γ
| CEScope_LetRec1 : forall Γ f vl C e2,
    EECTX Γh ⊢ C ∷ (S (length vl) + Γ) -> 
    EXP (S Γ) ⊢ e2 ->
    EECTX Γh ⊢ CLetRec1 f vl C e2 ∷ Γ
| CEScope_LetRec2 : forall Γ f vl e1 C,
    EXP S (length vl) + Γ ⊢ e1 ->
    EECTX Γh ⊢ C ∷ (S Γ) ->
    EECTX Γh ⊢ CLetRec2 f vl e1 C ∷ Γ
| CEScope_Plus1 : forall Γ C e2,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e2 ->
    EECTX Γh ⊢ CPlus1 C e2 ∷ Γ
| CEScope_Plus2 : forall Γ e1 C,
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ C ∷ Γ -> 
    EECTX Γh ⊢ CPlus2 e1 C ∷ Γ
| CEScope_If1 : forall Γ C e2 e3,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e2 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CIf1 C e2 e3 ∷ Γ
| CEScope_If2 : forall Γ C e1 e3,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e1 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CIf2 e1 C e3 ∷ Γ
| CEScope_If3 : forall Γ C e1 e2,
    EECTX Γh ⊢ C ∷ Γ -> 
    EXP Γ ⊢ e1 ->
    EXP Γ ⊢ e2 ->
    EECTX Γh ⊢ CIf3 e1 e2 C ∷ Γ
| CEScope_val : forall C Γ, VECTX Γh ⊢ C ∷ Γ -> EECTX Γh ⊢ C ∷ Γ
with VECtxScope (Γh : nat) : nat -> Ctx -> Prop :=
| CEScope_RecFun : forall Γ vl C,
    EECTX Γh ⊢ C ∷ (S (length vl) + Γ) ->
    VECTX Γh ⊢ CFun vl C ∷ Γ
where
"'EECTX' Γh ⊢ C ∷ Γ" := (EECtxScope Γh Γ C)
and
"'VECTX' Γh ⊢ C ∷ Γ" := (VECtxScope Γh Γ C).

Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e) /\
    (VECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     VAL Γ ⊢ plug C e).
Proof.
  induction C;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  * constructor. apply IHC; auto. inversion H1. subst. auto.
  * rewrite indexed_to_forall in H5. apply H5; auto.
  * apply nth_possibilities with (def := ELit 0) in H1 as H1'. destruct H1'.
    - destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7; auto.
    - destruct H2. rewrite H2 in *. remember (i - length l1) as i'. destruct i'.
      + simpl. apply IHC; auto.
      + simpl. rewrite indexed_to_forall in H8. apply H8; auto. simpl in H3. lia.
Qed.

Lemma plugc_preserves_scope_exp : forall {Γh Couter Γ Cinner Γ'},
    (EECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     EECTX Γh ⊢ plugc Couter Cinner ∷ Γ) /\
    (VECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     VECTX Γh ⊢ plugc Couter Cinner ∷ Γ).
Proof.
  induction Couter;
    split;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  * constructor. eapply IHCouter; eauto. inversion H. inversion H2. subst. auto.
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
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet [RLetRec [RPlus  RIf ] ] ] ] ] ] ] ] ].
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
    - apply RFun. reflexivity.
      apply IHC; auto.
      now inversion H1.
    - apply RApp; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RApp; auto.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H7. auto.
        ** simpl. apply IHC. auto.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H8. auto.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLetRec; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLetRec; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RPlus; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RPlus; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RIf; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RIf; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RIf; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
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

Local Definition dummyv := "foo"%string.
Local Definition dummyf := ("foo"%string, 0).

Fixpoint default_names (e : Exp) : Exp :=
match e with
 | ELit l => e
 | EVar n => EVar n
 | EFunId n => EFunId n
 | EFun vl e => EFun (map (fun _ => dummyv) vl) (default_names e)
 | EApp exp l => EApp (default_names exp) (map default_names l)
 | ELet v e1 e2 => ELet dummyv (default_names e1) (default_names e2)
 | ELetRec f vl b e => ELetRec dummyf (map (fun _ => dummyv) vl) (default_names b) (default_names e)
 | EPlus e1 e2 => EPlus (default_names e1) (default_names e2)
 | EIf e1 e2 e3 => EIf (default_names e1) (default_names e2) (default_names e3)
end.

Lemma default_value : forall v,
  is_value v <-> is_value (default_names v).
Proof.
  split; intros; destruct v; simpl in H; try inversion_is_value; try constructor.
  all: inversion H.
Qed.

Lemma default_value_impl : forall v,
  is_value v -> is_value (default_names v).
Proof.
  apply default_value.
Qed.

Global Hint Resolve default_value_impl : core.

Lemma default_value_rev : forall v,
  is_value (default_names v) -> is_value v.
Proof.
  apply default_value.
Qed.

Lemma default_names_helper l:
  (forall e : Exp, In e l -> is_value e)
->
  (forall e : Exp, In e (map default_names l) -> is_value e).
Proof.
  induction l; intros; subst. inversion H0.
  destruct (In_dec Exp_eq_dec e (map default_names l)) eqn:P.
  * apply IHl. intros. apply H. now constructor 2. clear P. auto.
  * inversion H0. 2: congruence. subst.
    epose proof (H a _). now apply -> default_value. Unshelve. constructor. auto.
Qed.

Definition default_name_frame (f : Frame) : Frame :=
match f with
 | FApp1 l => FApp1 (map default_names l)
 | FApp2 v l1 l2 => 
          FApp2 (default_names v) (map default_names l1) (map default_names l2)
 | FLet v e2 => FLet dummyv (default_names e2)
 | FPlus1 e2 => FPlus1 (default_names e2)
 | FPlus2 v => FPlus2 (default_names v)
 | FIf e2 e3 => FIf (default_names e2) (default_names e3)
end.

Lemma double_default e :
  default_names e = default_names (default_names e).
Proof.
  induction e using Exp_ind2 with (Q := fun l => Forall (fun e => default_names e = default_names (default_names e)) l); auto.
  * simpl. rewrite map_map, <- IHe. auto.
  * simpl. erewrite map_map, <- IHe. erewrite map_ext_Forall. 2: exact IHe0. auto.
  * simpl. rewrite <- IHe1, <- IHe2. auto.
  * simpl. rewrite <- IHe1, <- IHe2, map_map. auto.
  * simpl. rewrite <- IHe1, <- IHe2. auto.
  * simpl. rewrite <- IHe1, <- IHe2, <- IHe3. auto.
Qed.

Definition default_names_sub (ξ : Substitution) : Substitution :=
  fun n => match (ξ n) with
           | inl exp => inl (default_names exp)
           | inr n' => inr n'
           end.

Lemma rename_id_default :
  forall e ρ, rename ρ (default_names e) = default_names (rename ρ e).
Proof.
  induction e using Exp_ind2 with (Q := fun l => forall ρ, Forall (fun e => rename ρ (default_names e) = default_names (rename ρ e)) l); intros; auto; simpl.
  * f_equiv. now rewrite IHe, map_length.
  * rewrite IHe, map_map, map_map. erewrite map_ext_Forall. 2: apply IHe0. reflexivity.
  * now rewrite IHe1, IHe2.
  * now rewrite map_length, IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2, IHe3.
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
  induction e2 using Exp_ind2 with (Q := fun l => forall ξ, Forall (fun e2 => default_names e2.[ξ] = (default_names e2).[default_names_sub ξ]) l); intros; simpl; auto.
  * unfold default_names_sub; destruct (ξ n); auto; apply double_default.
  * unfold default_names_sub; destruct (ξ n); auto; apply double_default.
  * simpl. f_equiv. rewrite default_names_upn, default_names_up, IHe2. rewrite map_length. auto.
  * simpl. rewrite IHe2, map_map, map_map. erewrite map_ext_Forall. reflexivity. apply IHe0.
  * now rewrite IHe2_1, default_names_up, IHe2_2.
  * rewrite map_length. now rewrite default_names_upn, default_names_up, IHe2_1, default_names_up, IHe2_2.
  * now rewrite IHe2_1, IHe2_2.
  * now rewrite IHe2_1, IHe2_2, IHe2_3.
Qed.

Lemma is_value_alpha :
  forall v, is_value v <-> is_value (default_names v).
Proof.
  split; intros. induction H; constructor.
  induction v; try constructor; inversion H.
Qed.

Lemma Forall_map T (l : list T) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  apply IHl; auto.
Qed.

Lemma map_Forall T (l : list T) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  eapply IHl; eauto.
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

Theorem alpha_eval_k :
  forall k e fs, | fs, e | k ↓ <-> | map default_name_frame fs, default_names e | k ↓.
Proof.
  split.
  { generalize dependent e. generalize dependent fs.
    induction k; intros; simpl; inversion H; subst.
    * constructor. now apply -> default_value.
    * constructor. auto.
    * constructor; auto. destruct e; try inversion_is_value; simpl; try congruence.
    * simpl. econstructor; auto.
      replace (FPlus2 (default_names e) :: map default_name_frame fs0) with
                (map default_name_frame (FPlus2 e ::fs0)) by auto.
      apply IHk. auto.
    * simpl. constructor. eapply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H4. rewrite alpha_helper in H4.
      replace (default_names e .: idsubst) with (default_names_sub (e .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto. apply IHk in H3. rewrite alpha_helper in H3.
      replace (EFun (map (fun _ : Var => dummyv) vl)
                      (default_names b) .: idsubst) with (default_names_sub (EFun vl b .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto. now apply IHk in H4.
    * simpl. constructor; auto. apply IHk in H3. rewrite alpha_helper in H3.
      replace (EFun [] (default_names e0) .: idsubst) with (default_names_sub (EFun [] e0 .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto.
      - apply Forall_map; auto.
      - apply IHk in H5. simpl in H5. rewrite map_app in H5. auto.
    * simpl. constructor; auto.
      - apply Forall_map; auto.
      - do 2 rewrite map_length. lia.
      - apply IHk in H6. rewrite alpha_helper in H6.
        replace (list_subst
                      (EFun (map (fun _ : Var => dummyv) vl)
                         (default_names e0)
                       :: map default_names vs ++ [default_names e])
                      idsubst) with (default_names_sub
                           (list_subst (EFun vl e0 :: vs ++ [e])
                              idsubst)). auto.
        replace [default_names e] with (map default_names [e]) by auto.
        rewrite <- map_app, alpha_list_subst. auto.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
  }
  { generalize dependent e. generalize dependent fs.
    induction k; intros; simpl; inversion H; subst.
    * apply eq_sym, map_eq_nil in H0. subst. constructor. now apply default_value.
    * destruct e; inversion H1. destruct fs; inversion H0.
      destruct f; inversion H5. constructor. subst. apply IHk. auto.
    * destruct fs; inversion H0. destruct f; inversion H4. subst.
      apply IHk in H5. destruct e. destruct l.
      simpl in H3. congruence.
      all: constructor; try congruence; try inversion H2.
      all: constructor.
    * destruct fs; inversion H0. destruct f; inversion H3. subst.
      replace (FPlus2 (default_names e) :: map default_name_frame fs) with
              (map default_name_frame (FPlus2 e::fs)) in H4 by auto. apply IHk in H4.
      constructor; auto. now apply default_value.
    * destruct e; inversion H1. destruct fs; inversion H0.
      destruct f; inversion H5. subst. destruct v; inversion H7. subst.
      constructor. now apply IHk.
    * destruct fs; inversion H0. destruct f; inversion H3; subst.
      apply default_value in H2. constructor; auto. apply IHk.
      now rewrite alpha_helper, <- scons_alpha.
    * destruct e; inversion H0; subst. constructor. apply IHk.
      now rewrite alpha_helper, <- scons_alpha.
    * destruct fs; inversion H0. destruct f; inversion H3. destruct l; inversion H6.
      subst. apply term_app_start; auto. now apply default_value.
    * destruct e; inversion H1. destruct fs; inversion H0. destruct f; inversion H6.
      subst. destruct l; inversion H8. inversion H1. destruct vl; inversion H4.
      constructor. apply IHk. now rewrite alpha_helper, <- scons_alpha.
    * destruct fs; inversion H0. destruct f; inversion H4. destruct l1; inversion H8.
      subst. apply default_value in H2. apply default_value in H'.
      constructor; auto. eapply map_Forall; eauto. apply default_value.
      apply IHk. simpl. rewrite map_app. auto.
    * destruct fs; inversion H0. destruct f; inversion H5. destruct l1; inversion H9.
      destruct v; inversion H8. subst. apply default_value in H4. constructor; auto.
      eapply map_Forall. 2: exact H2. apply default_value.
      do 2 rewrite map_length in H3. auto.
      apply IHk. rewrite alpha_helper, alpha_list_subst. simpl. now rewrite map_app.
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
    1-2: do 2 constructor; now try rewrite <- H.
    specialize (H2 (plugc C (CFun vl' CHole))).
    repeat rewrite <- plug_assoc in H2.
    cbn in H2.
    apply H2.
    eapply plugc_preserves_scope_exp; eauto.
    do 2 constructor. rewrite H. constructor.
    shelve.
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
    1-2: constructor; auto.
    clear H5 H9 H4 H8.
    assert (EECTX Γ ⊢ plugc C (CLet1 x CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX S Γ ⊢ plugc C (CLet2 x e1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply H7 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2.
    shelve.
  * unfold CompatibleLetRec.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: rewrite H in H1; constructor; auto.
    clear H5 H9 H6 H10.
    assert (EECTX S (length vl) + Γ ⊢ plugc C (CLetRec1 f vl CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX S Γ ⊢ plugc C (CLetRec2 f vl b1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H7 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply H8 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2.
    shelve.
  * unfold CompatiblePlus.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: constructor; auto.
    clear H4 H8 H5 H9.
    assert (EECTX Γ ⊢ plugc C (CPlus1 CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX Γ ⊢ plugc C (CPlus2 e1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H7 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. now simpl.
  * unfold CompatibleIf.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: constructor; auto.
    clear H7 H12 H8 H13 H5 H14.
    assert (EECTX Γ ⊢ plugc C (CIf1 CHole e2 e3) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H9 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX Γ ⊢ plugc C (CIf2 e1' CHole e3) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H10 in HC_e2. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    assert (EECTX Γ ⊢ plugc C (CIf3 e1' e2' CHole) ∷ 0) as HC_e3.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H11 in HC_e3. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    rewrite <- plug_assoc in HC_e3. simpl in HC_e3. auto.
Unshelve.
  2-3: exact (ELit 0).
  apply alpha_eval in H4; apply alpha_eval; rewrite default_context in *;
       simpl in *; rewrite map_const in *; rewrite <- H; auto.

  apply alpha_eval. apply alpha_eval in HC_e2. rewrite default_context in *. exact HC_e2.

  apply alpha_eval. apply alpha_eval in HC_e2. rewrite default_context in *.
  simpl in *; rewrite map_const in *; rewrite <- H; auto.
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

Lemma CIU_beta_value : forall {Γ e2 x v},
    EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
    (CIU_open Γ e2.[v/] (ELet x v e2) /\ 
     CIU_open Γ (ELet x v e2) e2.[v/]).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU.
  intuition idtac.
  1,5: apply -> subst_preserves_scope_exp; try eassumption;
    apply -> subst_preserves_scope_exp; eauto.
  1,3: simpl; constructor; [ constructor; apply -> subst_preserves_scope_val; eauto |
                             apply -> subst_preserves_scope_exp; eauto ].
  destruct H3. exists (S (S x0)). simpl. apply term_let.
  pose proof (subst_preserves_scope_val v Γ). destruct H4.
  clear H5. specialize (H4 H0 0 ξ H1). apply Valclosed_is_value in H4. constructor; auto.
  rewrite subst_comp, subst_extend.
  now rewrite subst_comp, scons_substcomp, substcomp_id_l in H3.

  destruct H3. simpl in H3. inversion H3; try inversion_is_value. subst.
  pose proof (subst_preserves_scope_val v Γ). destruct H4.
  clear H5. specialize (H4 H0 0 ξ H1). apply Valclosed_is_value in H4.
  inversion H9; subst.
  rewrite subst_comp, subst_extend in H12.
  rewrite subst_comp, scons_substcomp, substcomp_id_l. eexists. exact H12.

  all: rewrite <- H5 in H4; inversion H4.
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
  epose proof (@CIU_beta_value Γ e1 "X"%string v Hscope_e1 _).
  epose proof (@CIU_beta_value Γ e2 "X"%string v Hscope_e2 _).
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
    replace e1.[ξ] with e1.[e/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp. rewrite scons_substcomp_core.
      rewrite (vclosed_ignores_sub e); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    replace e2.[ξ] with e2.[e/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp. rewrite scons_substcomp_core.
      rewrite (vclosed_ignores_sub e); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    apply IHΓ.
    apply CTX_closed_under_substitution; auto; revgoals.
    + specialize (H0 0 ltac:(lia)).
      simpl. replace e with (e.[idsubst]) by auto.
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
        rewrite escoped_ignores_sub; auto. destruct HR'.
        eapply H3 with (e1:=e1) (e2:=e2); eauto.
      }
      replace e2.[ξ] with e2; revgoals.
      { replace ξ with (upn 0 ξ) by auto.
        rewrite escoped_ignores_sub; auto. destruct HR'.
        eapply H3 with (e1:=e1) (e2:=e2); eauto.
      }
      clear H0.
      generalize dependent e2. generalize dependent e1. generalize dependent F.
      induction F; intros.
      * destruct HR'. destruct H, H. apply (H4 CHole); auto. constructor.
      * apply put_back in H2. destruct H2. apply put_back_rev; auto.
        eapply IHF. 2: exact H0. now inversion H1.
        destruct HR'. inversion H1; subst. inversion H. inversion H5.
        destruct a; inversion H7; subst.
        -- simpl. apply CTX_IsPreCtxRel; auto. apply forall_biforall_refl.
           apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H12.
           now apply H12.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           ++ apply Forall_app. split; auto. eapply Forall_impl. 2: exact H16.
              intros. now constructor.
           ++ apply Forall_app. split; auto. eapply Forall_impl. 2: exact H16.
              intros. now constructor.
           ++ now constructor.
           ++ now constructor.
           ++ apply CTX_refl. now constructor.
           ++ apply biforall_app. 2: constructor; auto.
              all: apply forall_biforall_refl; apply Forall_forall; 
                   intros; apply CTX_refl; rewrite Forall_forall in H15, H16.
              constructor. now apply H16.
              now apply H15.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto. 3: apply CTX_refl. all: now constructor.
        -- simpl. apply CTX_IsPreCtxRel; auto. 1-2: now apply CTX_refl.
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

Definition equivalent_exps (e1 e2 : Exp) (R : Exp -> Exp -> Prop) : Prop :=
  forall v1, ⟨ [], e1 ⟩ -->* v1 -> (exists v2, ⟨ [], e2 ⟩ -->* v2 /\ R v1 v2).

Fixpoint equivalent_values (n : nat) (v1 v2 : Exp) : Prop :=
match n with
| 0 => True
| S n' =>
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => forall vals, Forall (fun v => VALCLOSED v) vals ->
    length vals = length vl1 -> length vals = length vl2 ->
    equivalent_exps (b1.[list_subst (EFun vl1 b1::vals) idsubst]) (b2.[list_subst (EFun vl2 b2::vals) idsubst]) (equivalent_values n')
  | _, _ => False
  end
end.

Definition eq_exps (e1 e2 : Exp) := forall n, equivalent_exps e1 e2 (equivalent_values n).


Theorem CIU_eval : forall e1 v,
  EXPCLOSED e1 ->
  ⟨ [], e1 ⟩ -->* v -> CIU e1 v /\ CIU v e1.
Proof.
  intros. split. split. 2: split. auto.
  apply step_any_closedness in H0; auto. 1-2: now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  eapply terminates_step_any. 2: exact H3. eexists. exact H2.

  split. 2: split. 2: auto.
  apply step_any_closedness in H0; auto. 1-2: now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  exists (x + x0).
  eapply term_step_term. exact H3. 2: lia. replace (x + x0 - x0) with x by lia. exact H2.
Qed.

Corollary CTX_eval : forall e1 v,
  EXPCLOSED e1 ->
  ⟨ [], e1 ⟩ -->* v -> CTX 0 e1 v /\ CTX 0 v e1.
Proof.
  intros. split; apply CIU_iff_CTX; intro; intros.
  rewrite eclosed_ignores_sub, vclosed_ignores_sub.
  4: rewrite vclosed_ignores_sub, eclosed_ignores_sub.
  1, 4: pose proof (CIU_eval _ _ H H0). all: auto. 1-2: apply H2.
  all: apply step_any_closedness in H0; auto; constructor.
Qed.

Lemma CIU_beta_values : forall {Γ e vl vals},
    VAL Γ ⊢ EFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals ->
    (CIU_open Γ (e.[list_subst (EFun vl e :: vals) idsubst]) (EApp (EFun vl e) vals) /\ 
     CIU_open Γ (EApp (EFun vl e) vals) (e.[list_subst (EFun vl e :: vals) idsubst])).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU. inversion H.
  intuition idtac.
  1,5: apply -> subst_preserves_scope_exp; try eassumption;
    apply -> subst_preserves_scope_exp; eauto.
  * replace (S (length vl) + Γ) with (length (EFun vl e :: vals) + Γ).
    2: simpl; lia.
    eapply scoped_list_subscoped. constructor; auto.
    apply scope_idsubst.
  * replace (S (length vl) + Γ) with (length (EFun vl e :: vals) + Γ).
    2: simpl; lia.
    eapply scoped_list_subscoped. constructor; auto.
    apply scope_idsubst.
  * simpl. constructor. do 2 constructor.
    apply -> subst_preserves_scope_exp; eauto. do 2 rewrite Nat.add_succ_l.
    now apply up_scope, upn_scope.
    intros. rewrite map_length in H6. rewrite indexed_to_forall in H0.
    replace (ELit 0) with ((ELit 0).[ξ]) by auto. rewrite map_nth.
    apply -> subst_preserves_scope_exp; eauto.
  * destruct H7. simpl.
    destruct vals.
    - exists (2 + x). constructor.
      simpl. apply length_zero_iff_nil in H1. subst. simpl in *. constructor. simpl in *.
      rewrite subst_comp in *.
      rewrite subst_extend. rewrite scons_substcomp in H7. simpl in H7. auto.
    - simpl in *. subst. inversion H0. subst.
      assert (Forall is_value (e1.[ξ]::map (subst ξ) vals)). { 
        constructor. apply Valclosed_is_value.
        eapply subst_preserves_scope_val in H8. exact H8. auto.
        
        clear H0 H1 H3 H6 H7 H8 F x H e1 vl e. induction vals.
        constructor.
        inversion H9. constructor. 2: apply IHvals; auto.
        subst. apply Valclosed_is_value. eapply subst_preserves_scope_val in H1. exact H1.
        auto.
      }
      destruct (length vals) eqn:Lvals.
      + apply length_zero_iff_nil in Lvals. subst.
        simpl in *. exists (3 + x). do 2 constructor. constructor.
        inversion H2. subst. constructor; auto. Opaque list_subst.
        rewrite subst_comp in *. simpl in *. rewrite H1 in *.
        replace (up_subst (upn 1 ξ)) with (upn 2 ξ) by auto.
        rewrite subst_list_extend; auto. do 2 rewrite scons_substcomp in H7. simpl in H7.
        Transparent list_subst. simpl. rewrite H1 in H7. simpl in H7. auto.
      + apply eq_sym, last_element_exists in Lvals as LL. destruct LL, H4. subst.
        inversion H2. subst. rewrite map_app in H12. rewrite app_length in Lvals.
        simpl in Lvals.
        apply Forall_app in H12. destruct H12. inversion H10. subst.
        epose proof (eval_app_partial_core (map (subst ξ) x0) [] vl 
                          (e.[up_subst (upn (Datatypes.length vl) ξ)]) x1.[ξ] 
                          e1.[ξ] F [] ltac:(auto) H4 H11). simpl in H12.
        rewrite subst_comp in *. do 2 rewrite scons_substcomp in H7.
        rewrite scons_substcomp_list in H7. simpl in H7.
        assert (⟨ FApp2 (EFun vl e.[up_subst (upn (Datatypes.length vl) ξ)]) []
              (e1.[ξ] :: map (subst ξ) x0) :: F, x1.[ξ] ⟩ -[1]->
              ⟨F,
      e.[EFun vl e.[up_subst (upn (Datatypes.length vl) ξ)]
        .: e1.[ξ] .: list_subst (map (subst ξ) (x0 ++ [x1])) (idsubst >> ξ)]⟩). {
          econstructor. constructor; auto. simpl. rewrite map_length. lia.
          simpl. rewrite subst_comp. repeat fold_upn.
          replace (EFun vl e.[upn (S (Datatypes.length vl)) ξ]
   .: e1.[ξ] .: list_subst (map (subst ξ) x0 ++ [x1.[ξ]]) idsubst) with
          (list_subst (EFun vl e.[upn (S (Datatypes.length vl)) ξ] :: e1.[ξ] :: (map (subst ξ) x0 ++ [x1.[ξ]])) idsubst) by auto.
          rewrite subst_list_extend; auto. 2: simpl; rewrite app_length, map_length; simpl; lia.
           simpl. rewrite substcomp_id_l, map_app. constructor.
        }
        epose proof (transitive_eval _ _ _ _ _ H12 _ _ _ H13).
        eapply term_step_term_plus in H16. 2: exact H7.
        exists (2 + (S (Datatypes.length (map (subst ξ) x0)) + 1 + x)).
        do 2 constructor. constructor. rewrite map_app. exact H16.
  * simpl. constructor. do 2 constructor.
    apply -> subst_preserves_scope_exp; eauto. do 2 rewrite Nat.add_succ_l.
    now apply up_scope, upn_scope.
    intros. rewrite map_length in H6. rewrite indexed_to_forall in H0.
    replace (ELit 0) with ((ELit 0).[ξ]) by auto. rewrite map_nth.
    apply -> subst_preserves_scope_exp; eauto.
  * rewrite subst_comp, scons_substcomp_list, substcomp_id_l.
    destruct H7. simpl in H7. inversion H7; subst; try inversion_is_value.
    destruct vals.
    - inversion H12; subst; try inversion_is_value. simpl in *.
      rewrite subst_comp, subst_extend in H10. exists k0. auto.
    - Opaque list_subst.
      assert (Forall is_value (e0.[ξ]::map (subst ξ) vals)). { 
        inversion H0. subst.
        constructor. apply Valclosed_is_value. 
        eapply subst_preserves_scope_val in H8. exact H8. auto.
        
        clear H0 H1 H3 H6 H7 H8 H12 F H vl e0 e. induction vals.
        constructor.
        inversion H9. constructor. 2: apply IHvals; auto.
        subst. apply Valclosed_is_value. eapply subst_preserves_scope_val in H1. exact H1.
        auto.
      } inversion H2. subst.
      destruct (length vals) eqn:Lvals.
      + apply length_zero_iff_nil in Lvals. subst.
        inversion H12; subst; try inversion_is_value. simpl in *.
        inversion H16; try rewrite <- H4 in *; try inversion_is_value.
        subst. repeat fold_upn. repeat fold_upn_hyp.
        rewrite subst_comp, subst_list_extend in H21. simpl in H21. exists k. auto.
        simpl. lia.
      + apply eq_sym, last_element_exists in Lvals as LL. destruct LL, H4. subst.
        rewrite app_length in Lvals; simpl in Lvals. rewrite map_app in H10.
        apply Forall_app in H10. destruct H10.
        epose proof (eval_app_partial_core (map (subst ξ) x) [] vl 
                          (e.[up_subst (upn (Datatypes.length vl) ξ)]) x0.[ξ] 
                          e0.[ξ] F [] ltac:(auto) H4 H9).
        inversion H12; subst; try inversion_is_value. rewrite map_app in H18.
        eapply (terminates_step_any_2 _ _ _ _ H18) in H10 as H10'. simpl in H10'.
        inversion H8. subst.
        inversion H10'; subst; try rewrite <- H11 in *; try inversion_is_value.
        repeat fold_upn_hyp. rewrite subst_comp, subst_list_extend in H25. simpl in H25.
        simpl. rewrite map_app. eexists. exact H25.
        simpl in *. rewrite app_length, map_length in *. simpl. lia.
      Transparent list_subst.
Qed.

Corollary CTX_beta_values : forall {Γ e vl vals},
    VAL Γ ⊢ EFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals ->
    (CTX Γ (e.[list_subst (EFun vl e :: vals) idsubst]) (EApp (EFun vl e) vals) /\ 
     CTX Γ (EApp (EFun vl e) vals) (e.[list_subst (EFun vl e :: vals) idsubst])).
Proof.
  intros. split; apply CIU_iff_CTX, CIU_beta_values; auto.
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
  * unfold equivalent_exps. intros. cbn. destruct H, H.
    apply ex_intro in H0 as H0'. apply -> terminates_eq_terminates_sem in H0'.
    pose proof (H1 CHole ltac:(constructor) H0'). simpl in H3.
    apply terminates_eq_terminates_sem in H3. destruct H3. exists x. split; auto.
    clear H0'.
    apply result_is_value_any in H0 as Hv. apply result_is_value_any in H3 as Hv'.
    destruct v1; try inversion_is_value.
    - destruct x; try inversion_is_value.
      + epose proof (H1 (CIf1 (CPlus1 CHole (ELit (-l))) (ELit 0) inf) _ _).
        simpl in H4. destruct H4. inversion H4; try inversion_is_value. subst.
        inversion H10; try inversion_is_value. subst.
        destruct H3, H5. eapply frame_indep_nil in H5.
        eapply terminates_step_any_2 in H9. 2: exact H5.
        inversion H9. inversion H13. inversion H18; subst.
        ** lia.
        ** apply inf_diverges in H26. contradiction.
      + epose proof (H1 (CIf1 (CPlus1 CHole (ELit (-l))) (ELit 0) inf) _ _).
        simpl in H4. destruct H4. inversion H4; try inversion_is_value. subst.
        inversion H10; try inversion_is_value. subst.
        destruct H3, H5. eapply frame_indep_nil in H5.
        eapply terminates_step_any_2 in H9. 2: exact H5.
        inversion H9. inversion H13.
      Unshelve.
        1-3: repeat constructor. 1, 2, 4, 5 : inversion H4.
        ** simpl. destruct H0, H4. exists (5 + x).
           constructor. apply term_plus. eapply term_step_term with (k := x).
           eapply frame_indep_nil in H4. exact H4. replace (S (S (S x)) - x) with 3 by lia.
           do 2 constructor. replace (Z.add l (Z.opp l)) with 0%Z by lia.
           do 3 constructor. lia.
        ** simpl. destruct H0, H4. exists (5 + x0).
           constructor. apply term_plus. eapply term_step_term with (k := x0).
           eapply frame_indep_nil in H4. exact H4. replace (S (S (S x0)) - x0) with 3 by lia.
           do 2 constructor. replace (Z.add l (Z.opp l)) with 0%Z by lia.
           do 3 constructor. lia.
    - destruct x; try inversion_is_value.
      + apply ex_intro in H3 as H3'. apply -> terminates_eq_terminates_sem in H3'.
        destruct P.
        epose proof (H5 (CIf1 (CPlus1 CHole (ELit (-l))) (ELit 0) inf) _ _).
        simpl in H6. destruct H6. inversion H6; try inversion_is_value. subst.
        inversion H12; try inversion_is_value. subst.
        destruct H0, H7. eapply frame_indep_nil in H7.
        eapply terminates_step_any_2 in H11. 2: exact H7.
        inversion H11. inversion H15.
      + intros. apply IHn.
        --
        assert (CTX 0 e1 e2). {
          split. split. all: auto.
        }
        assert (CTX 0 (EFun vl0 x) (EFun vl v1)). {
          apply CTX_eval in H0; auto. apply CTX_eval in H3; auto.
          assert (Transitive (CTX 0)). { apply CTX_IsPreCtxRel. }
          destruct H0, H3.
          epose proof (H8 _ _ _ H10 P). epose proof (H8 _ _ _ H11 H0). auto.
        }
        epose proof CTX_IsPreCtxRel. destruct H9 as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet [RLetRec [RPlus RIf]]]]]]]]]. unfold CompatibleApp in RApp.
        assert (VALCLOSED (EFun vl v1)). {
          apply step_any_closedness in H0. now inversion H0. constructor. auto.
        }
        assert (VALCLOSED (EFun vl0 x)). {
          apply step_any_closedness in H3. now inversion H3. constructor. auto.
        }
        apply RApp with (vals1 := vals) (vals2 := vals) in H8; auto.
        4-5: now constructor.
        ** epose proof (CTX_beta_values H9 H4 (eq_sym H5)). destruct H11.
           epose proof (CTX_beta_values H10 H4 (eq_sym H6)). destruct H13.
           epose proof (Rtrans 0 _ _ _ H13 H8).
           epose proof (Rtrans 0 _ _ _ H15 H12). auto.
        ** eapply Forall_impl. 2: exact H4. intros. now constructor.
        ** eapply Forall_impl. 2: exact H4. intros. now constructor.
        ** apply forall_biforall_refl. apply Forall_forall. intros. apply CTX_refl.
           rewrite Forall_forall in H4. constructor. now apply H4.
        --
        assert (CTX 0 e1 e2). {
          split. split. all: auto.
        }
        assert (CTX 0 (EFun vl v1) (EFun vl0 x)). {
          apply CTX_eval in H0; auto. apply CTX_eval in H3; auto.
          assert (Transitive (CTX 0)). { apply CTX_IsPreCtxRel. }
          destruct H0, H3.
          epose proof (H8 _ _ _ H9 H7). epose proof (H8 _ _ _ H11 H3). auto.
        }
        epose proof CTX_IsPreCtxRel. destruct H9 as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet [RLetRec [RPlus RIf]]]]]]]]]. unfold CompatibleApp in RApp.
        assert (VALCLOSED (EFun vl v1)). {
          apply step_any_closedness in H0. now inversion H0. constructor. auto.
        }
        assert (VALCLOSED (EFun vl0 x)). {
          apply step_any_closedness in H3. now inversion H3. constructor. auto.
        }
        apply RApp with (vals1 := vals) (vals2 := vals) in H8; auto.
        4-5: now constructor.
        ** epose proof (CTX_beta_values H9 H4 (eq_sym H5)). destruct H11.
           epose proof (CTX_beta_values H10 H4 (eq_sym H6)). destruct H13.
           epose proof (Rtrans 0 _ _ _ H11 H8).
           epose proof (Rtrans 0 _ _ _ H15 H14). auto.
        ** eapply Forall_impl. 2: exact H4. intros. now constructor.
        ** eapply Forall_impl. 2: exact H4. intros. now constructor.
        ** apply forall_biforall_refl. apply Forall_forall. intros. apply CTX_refl.
           rewrite Forall_forall in H4. constructor. now apply H4.
Unshelve.
  ++ repeat constructor. all: inversion H6.
  ++ simpl. destruct H3, H6. exists (5 + x).
     constructor. apply term_plus.
     eapply term_step_term with (k := x).
     eapply frame_indep_nil in H6. exact H6. replace (S (S (S x)) - x) with 3 by lia.
     constructor. auto. constructor. replace (Z.add l (Z.opp l)) with 0%Z by lia.
     do 3 constructor. lia.
Qed.

(** MAJOR RESULT: *)
Theorem terminating_implies_equivalence :
  forall e1 e2, CTX 0 e2 e1 -> CTX 0 e1 e2 -> eq_exps e1 e2 /\ eq_exps e2 e1.
Proof.
  intros. split; eapply terminating_implies_equivalence_helper; auto.
Qed.

(* Theorem equivalence_implies_terminating :
  forall e1 e2, EXPCLOSED e1 -> EXPCLOSED e2 -> eq_exps e1 e2 -> eq_exps e2 e1 ->
    (CIU e1 e2 /\ CIU e2 e1).
Proof.
  intros. unfold CIU, eq_exps, equivalent_exps in *.
  repeat split; auto; intros.
  * apply terminates_eq_terminates_sem in H4 as [v H4]. apply H1 in H4.
    destruct H4, H4. apply terminates_eq_terminates_sem. exists x; auto. auto.
  * apply terminates_eq_terminates_sem in H4 as [v H4]. apply H2 in H4.
    destruct H4, H4. apply terminates_eq_terminates_sem. exists x; auto. auto.
Qed. *)



Definition equivalent_exps2 (e1 e2 : Exp) (R : Exp -> Exp -> Prop) : Prop :=
  forall v1 Fs, FSCLOSED Fs -> ⟨ Fs, e1 ⟩ -->* v1 -> (exists v2, ⟨ Fs, e2 ⟩ -->* v2 /\ R v1 v2).

Fixpoint equivalent_values2 (n : nat) (v1 v2 : Exp) : Prop :=
match n with
| 0 => True
| S n' =>
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => forall vals, Forall (fun v => VALCLOSED v) vals ->
    length vals = length vl1 -> length vals = length vl2 ->
    equivalent_exps2 (b1.[list_subst (EFun vl1 b1::vals) idsubst]) (b2.[list_subst (EFun vl2 b2::vals) idsubst]) (equivalent_values2 n')
  | _, _ => False
  end
end.

Definition eq_exps2 (e1 e2 : Exp) :=
  equivalent_exps2 e1 e2 (fun v1 v2 => forall n, equivalent_values2 n v1 v2).

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
  * simpl. assert (is_value v1) as Vv1 by apply H1.
    assert (is_value x) as Vx by apply H7.
    destruct v1, x; try inversion_is_value.
    - assert (| Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], e1 | ↓) as T1. {
        destruct H1, H8. apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H8.
        assert (⟨ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], ELit l ⟩ -[3]-> ⟨[], ELit 0⟩).
        {
          econstructor. constructor. constructor.
          econstructor. constructor. rewrite Z.add_opp_diag_r.
          econstructor. constructor. constructor.
        }
        apply terminates_eq_terminates_sem. exists (ELit 0). split. constructor.
        exists (x + 3). eapply transitive_eval. exact H8. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) _ T1).
      destruct CONTRA.
      destruct H7, H9.
      apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H9.
      eapply terminates_step_any_2 in H8. 2: eauto.
      inversion H8. inversion H15. subst. inversion H20.
      + lia.
      + subst. apply inf_diverges in H21. contradiction.
    - assert (| Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], e1 | ↓) as T1. {
        destruct H1, H8. apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H8.
        assert (⟨ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], ELit l ⟩ -[3]-> ⟨[], ELit 0⟩).
        {
          econstructor. constructor. constructor.
          econstructor. constructor. rewrite Z.add_opp_diag_r.
          econstructor. constructor. constructor.
        }
        apply terminates_eq_terminates_sem. exists (ELit 0). split. constructor.
        exists (x0 + 3). eapply transitive_eval. exact H8. auto.
      }
      epose proof (CONTRA := H6 (Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) _ T1).
      destruct CONTRA.
      destruct H7, H9.
      apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H9.
      eapply terminates_step_any_2 in H8. 2: eauto.
      inversion H8. inversion H15.
    (* P : CIU e2 e1 -> is used only for the following subgoal for simplicity,
                        however, it should be possible to avoid it *)
    - assert (| Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], e2 | ↓) as T1. {
        destruct H7, H8. apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H8.
        assert (⟨ [FPlus1 (ELit (-l)); FIf (ELit 0) inf], ELit l ⟩ -[3]-> ⟨[], ELit 0⟩).
        {
          econstructor. constructor. constructor.
          econstructor. constructor. rewrite Z.add_opp_diag_r.
          econstructor. constructor. constructor.
        }
        apply terminates_eq_terminates_sem. exists (ELit 0). split. constructor.
        exists (x + 3). eapply transitive_eval. exact H8. auto.
      }
      epose proof (CONTRA := H5 (Fs ++ [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) _ T1).
      destruct CONTRA.
      destruct H1, H9.
      apply frame_indep_nil with (Fs' := [FPlus1 (ELit (-l)); FIf (ELit 0) inf]) in H9.
      eapply terminates_step_any_2 in H8. 2: eauto.
      inversion H8. inversion H15.
    - intros. unfold equivalent_exps2. intros.
      assert (⟨ Fs ++ [FApp1 vals] ++ Fs0, e1 ⟩ -->* v0) as T1'. {
        destruct H1, H13.
        apply frame_indep_nil with (Fs' := [FApp1 vals] ++ Fs0) in H13.
        
        assert (exists k, ⟨ [FApp1 vals] ++ Fs0, EFun vl v1 ⟩ -[k]->
                ⟨Fs0, v1.[EFun vl v1 .: list_subst vals idsubst]⟩). {
          apply app1_eval; auto. eapply Forall_impl. 2: exact H8.
          intros. now apply Valclosed_is_value.
        }
        destruct H14.
        epose proof (transitive_eval _ _ _ _ _ H13 _ _ _ H14).
        destruct H12, H16.
        epose proof (transitive_eval _ _ _ _ _ H15 _ _ _ H16).
        split; auto. eexists; eauto.
      }
      eapply ex_intro in T1' as T1.
      apply terminates_eq_terminates_sem in T1.
      epose proof (H6 (Fs ++ ([FApp1 vals] ++ Fs0)) _ T1).

      destruct H7, H14.
      apply frame_indep_nil with (Fs' := [FApp1 vals] ++ Fs0) in H14.
      assert (exists k, ⟨ [FApp1 vals] ++ Fs0, EFun vl0 x ⟩ -[k]->
                ⟨Fs0, x.[EFun vl0 x .: list_subst vals idsubst]⟩). {
        apply app1_eval; auto. eapply Forall_impl. 2: exact H8.
        intros. now apply Valclosed_is_value.
      }
      destruct H15, H13.
      eapply terminates_step_any_2 in H13. 2: exact H14.
      eapply terminates_step_any_2 in H13. 2: exact H15.
      apply terminates_in_k_eq_terminates_in_k_sem in H13. destruct H13, H13.
      exists x3. split.
      + split; auto. eexists. eassumption.
      + eapply IHn.
        3: { exact T1'. }
        ** apply Forall_app. split. 2: apply Forall_app; split.
           all: auto. do 2 constructor. eapply Forall_impl.
             intros. apply scoped_val. exact H17.
             auto.
        ** epose proof (transitive_eval _ _ _ _ _ H14 _ _ _ H15).
           epose proof (transitive_eval _ _ _ _ _ H17 _ _ _ H13).
           split; auto. eexists; eauto.
  Unshelve.
    all: apply Forall_app; split; auto.
    1-3: repeat constructor; inversion H8.
    apply Forall_app; split; auto.
    do 2 constructor. eapply Forall_impl.
    intros. apply scoped_val. exact H13.
    auto.
Qed.

Notation "e1 ≈[ Γ ]≈ e2" := (CTX Γ e1 e2 /\ CTX Γ e2 e1) (at level 70).
Notation "e1 ≈ e2" := (CTX 0 e1 e2 /\ CTX 0 e2 e1) (at level 70).

