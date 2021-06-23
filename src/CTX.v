Require Export CIU.

Import ListNotations.

Check fold_left.

Theorem fold_left_map :
  forall (T T2 T3 : Type) (l : list T) f (f2 : T -> T2 -> T3 -> T) d t2 t3,
  (forall a b t2 t3, f2 (f a b) t2 t3 = f (f2 a t2 t3) (f2 b t2 t3)) ->
  f2 (fold_left f l d) t2 t3 = fold_left f (map (fun x => f2 x t2 t3) l) (f2 d t2 t3).
Proof.
  induction l; intros; auto.
  intros. cbn.
  rewrite IHl; auto. rewrite H. auto.
Qed.

Definition Adequate (R : nat -> Exp -> Exp -> Prop) :=
  forall e1 e2, R 0 e1 e2 -> |[], e1| ↓ -> |[], e2| ↓.

Definition IsReflexive (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e,
  EXP Γ ⊢ e -> R Γ e e.

Definition CompatibleFun (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ vl vl' e1 e2, length vl = length vl' ->
    R (length vl + Γ) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl' e2).

Definition CompatibleRecFun (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f f' vl vl' e1 e2, length vl = length vl' ->
    R (S (length vl) + Γ) e1 e2 ->
    R Γ (ERecFun f vl e1) (ERecFun f' vl' e2).

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
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' -> EXP Γ ⊢ e3 -> EXP Γ ⊢ e3' -> (* is this needed? *)
  R Γ e1 e1' -> R Γ e2 e2' -> R Γ e3 e3' ->
  R Γ (EIf e1 e2 e3) (EIf e1' e2' e3').

Definition IsPreCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  (forall Γ e1 e2, R Γ e1 e2 -> EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\ CompatibleRecFun R /\ CompatibleApp R /\ CompatibleLet R/\ CompatibleLetRec R /\
  CompatiblePlus R /\ CompatibleIf R.

Definition IsCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  IsPreCtxRel R /\
  forall R', IsPreCtxRel R' ->
    forall Γ e1 e2, R' Γ e1 e2 -> R Γ e1 e2.


(* Lemma CTX_closed_under_substitution : forall {Γ e1 e2 vals CTX},
    IsCtxRel CTX ->
    Forall (fun v => VAL Γ ⊢ v) vals ->
    CTX (Γ ++ l) e1 e2 ->
    CTX Γ (subst ξ e1) (subst ξ e2).
Proof.
  intros Γ e1 e2 v CTX HCtx Hscope_v HCtx_e1e2.
  destruct HCtx as [HCtx Hbiggest].
  destruct HCtx as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RSeq RFactor]]]]]]].
  destruct (Rscope _ _ _ HCtx_e1e2) as [Hscope_e1 Hscope_e2].
  pose proof (CIU_beta_value Hscope_e1 Hscope_v).
  pose proof (CIU_beta_value Hscope_e2 Hscope_v).
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
  auto.
Qed. *)

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
  * unfold CompatibleRecFun.
    intros. auto.
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
  all: unfold Adequate, Transitive, IsReflexive, CompatibleFun, CompatibleRecFun,
    CompatibleApp, CompatibleLet, CompatibleLetRec, CompatiblePlus, CompatibleIf; intros.
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
  * apply CIU_iff_Erel in H11.
    now eapply H4.
  * apply CIU_iff_Erel in H14.
    eapply biforall_impl in H15.
    eapply H5; eauto.
    intros. now apply CIU_iff_Erel.
  * apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    now eapply H6.
  * apply CIU_iff_Erel in H15.
    apply CIU_iff_Erel in H16.
    now eapply H7.
  * apply CIU_iff_Erel in H14.
    apply CIU_iff_Erel in H15.
    now apply H8.
  * apply CIU_iff_Erel in H16.
    apply CIU_iff_Erel in H17.
    apply CIU_iff_Erel in H18.
    eapply H10; eauto.
Qed.

Inductive Ctx :=
| CHole
| CFun      (vl : list Var) (e : Ctx)
| CRecFun   (f : FunctionIdentifier) (vl : list Var) (e : Ctx)
| CAppFun   (exp : Ctx) (l : list Exp)
| CAppParam (exp : Exp) (l1 : list Exp) (c : Ctx) (l2 : list Exp)  (* one of the middle ones is a ctx *)
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
| CRecFun f vl e => ERecFun f vl (plug e p)
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
| CRecFun f vl e => CRecFun f vl (plugc e p)
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
| CEScope_Fun : forall Γ vl C,
    EECTX Γh ⊢ C ∷ (length vl + Γ) ->
    VECTX Γh ⊢ CFun vl C ∷ Γ
| CEScope_RecFun : forall Γ f vl C,
    EECTX Γh ⊢ C ∷ (S (length vl) + Γ) ->
    VECTX Γh ⊢ CRecFun f vl C ∷ Γ
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
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RRecFun [RApp [RLet [RLetRec [RPlus  RIf ] ] ] ] ] ] ] ] ] ].
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
    - apply RRecFun. reflexivity.
      apply IHC.
      inversion H1; auto.
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
             Search length nth cons app. epose (H11 (length l1) _). rewrite nth_middle in e. auto.
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
 | EVar n v => EVar n dummyv
 | EFunId n f => EFunId n dummyf
 | EFun vl e => EFun (map (fun _ => dummyv) vl) (default_names e)
 | ERecFun f vl e => ERecFun dummyf (map (fun _ => dummyv) vl) (default_names e)
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
  * simpl. f_equiv. rewrite default_names_upn, IHe2. rewrite map_length. auto.
  * simpl. f_equiv. rewrite default_names_upn, default_names_up, IHe2. rewrite map_length. auto.
  * simpl. rewrite IHe2, map_map, map_map. erewrite map_ext_Forall. reflexivity. apply IHe0.
  * now rewrite IHe2_1, default_names_up, IHe2_2.
  * rewrite map_length. now rewrite default_names_upn, default_names_up, IHe2_1, default_names_up, IHe2_2.
  * now rewrite IHe2_1, IHe2_2.
  * now rewrite IHe2_1, IHe2_2, IHe2_3.
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
      replace (ERecFun dummyf (map (fun _ : Var => dummyv) vl)
                      (default_names b) .: idsubst) with (default_names_sub (ERecFun f vl b .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto. now apply IHk in H4.
    * simpl. constructor; auto.
    * simpl. constructor; auto. apply IHk in H3. rewrite alpha_helper in H3.
      replace (ERecFun dummyf [] (default_names e0) .: idsubst) with (default_names_sub (ERecFun f [] e0 .: idsubst)). auto.
      unfold idsubst, default_names_sub. extensionality n. destruct n; auto.
    * simpl. constructor; auto.
      - admit. (* Provable, technical *)
      - apply IHk in H5. simpl in H5. rewrite map_app in H5. auto.
    * simpl. constructor; auto.
      - admit. (* Provable, technical *)
      - do 2 rewrite map_length. lia.
      - apply IHk in H6. rewrite alpha_helper in H6.
        replace (list_subst
                      (map default_names vs ++ [default_names e])
                      idsubst) with (default_names_sub
                           (list_subst (vs ++ [e]) idsubst)). auto.
        admit.
    * simpl. constructor; auto.
      - admit. (* Provable, technical *)
      - do 2 rewrite map_length. lia.
      - apply IHk in H6. rewrite alpha_helper in H6.
        replace (list_subst
                      (ERecFun dummyf (map (fun _ : Var => dummyv) vl)
                         (default_names e0)
                       :: map default_names vs ++ [default_names e])
                      idsubst) with (default_names_sub
                           (list_subst (ERecFun f vl e0 :: vs ++ [e])
                              idsubst)). auto.
        admit.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
    * simpl. constructor; auto. apply IHk in H3. exact H3.
  }
  { generalize dependent e. generalize dependent fs.
    induction k; intros; simpl; inversion H; subst.
    * apply eq_sym, map_eq_nil in H0. subst. constructor. now apply default_value.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
  }
Admitted.

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

Theorem map_const :
  forall {T T2} (l : list T) (a : T2), map (fun _ => a) l = repeat a (length l).
Proof.
  induction l; intros.
  auto.
  simpl. rewrite IHl. auto.
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
  * unfold CompatibleRecFun.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; now try rewrite <- H.
    specialize (H2 (plugc C (CRecFun f' vl' CHole))).
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
  3-4: exact (ELit 0).
  1-2: apply alpha_eval in H4; apply alpha_eval; rewrite default_context in *;
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

Lemma exists_CTX : exists R, IsCtxRel R.
Proof.
  exists CTX.
  apply CTX_IsCtxRel.
Qed.

Lemma CIU_beta_value : forall {Γ b vals} vl,
    length vl = length vals ->
    EXP (length vl) + Γ ⊢ b ->
    Forall (fun v => VAL Γ ⊢ v) vals ->
    (CIU_open Γ b.[list_subst vals idsubst] (EApp (EFun vl b) vals) /\ 
     CIU_open Γ (EApp (EFun vl b) vals) b.[list_subst vals idsubst]).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU.
  intuition idtac.
  - apply -> subst_preserves_scope_exp; try eassumption.
    apply -> subst_preserves_scope_exp; eauto.
    Search idsubst. intro. intros. Search list_subst.
    pose (list_subst_get_possibilities v vals idsubst). intuition; rewrite H5.
    rewrite indexed_to_forall in H1. apply H1. auto.
    unfold idsubst. lia.
  - simpl. constructor.
    + constructor. constructor.
      apply -> subst_preserves_scope_exp; eauto.
    + intros. replace (ELit 0) with ((ELit 0).[ξ]) by auto. rewrite map_nth.
      apply -> subst_preserves_scope_exp; eauto. rewrite indexed_to_forall in H1.
      constructor. apply H1. rewrite map_length in H3. auto.
  - simpl. admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma CTX_closed_under_substitution : forall {Γ e1 e2 v CTX},
    IsCtxRel CTX ->
    VAL Γ ⊢ v ->
    CTX (S Γ) e1 e2 ->
    CTX Γ e1.[v/] e2.[v/].
Proof.
  intros Γ e1 e2 v CTX HCtx Hscope_v HCtx_e1e2.
  destruct HCtx as [HCtx Hbiggest].
  destruct HCtx as [Rscope [Radequate [Rrefl [Rtrans [RFun [RRecFun [RApp [RLet [RLetRec [RPlus RIf]]]]]]]]]].
  destruct (Rscope _ _ _ HCtx_e1e2) as [Hscope_e1 Hscope_e2].
  epose proof (@CIU_beta_value Γ e1 [v] ["X"%string] (eq_refl _) Hscope_e1 _).
  epose proof (@CIU_beta_value Γ e2 [v] ["X"%string] (eq_refl _) Hscope_e2 _).
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
  apply RApp.
  1-4: constructor; constructor; auto.
  2: constructor; [ apply Rrefl; now constructor | constructor ].
  apply RFun; auto.
Unshelve.
  1-2: constructor; auto.
Qed.

Definition mk_exp (v : Exp + nat) :=
match v with
| inl e => e
| inr n => EVar n "x"%string
end.

Fixpoint make_Ctx (fs : FrameStack) : Ctx :=
match fs with
| [] => CHole
| x::xs => plugc (make_Ctx xs) 
           match x with
           | FApp1 l => CAppFun CHole l
           | FApp2 v p l1 l2 p2 => CAppParam v l1 CHole l2
           | FLet x e2 => CLet1 x CHole e2
           | FPlus1 e2 => CPlus1 CHole e2
           | FPlus2 v p => CPlus2 v CHole
           | FIf e2 e3 => CIf1 CHole e2 e3
          end
end.

(* Theorem make_Ctx_eval_equiv :
  forall fs e, | fs , e | ↓ -> | [], plug (make_Ctx fs) e | ↓.
Proof.

Admitted. *)

Theorem CIU_IsCtxRel : IsCtxRel CIU_open.
Proof.
  destruct exists_CTX as [R' HR'].
  eapply bigger_implies_IsCtxRel. 2: eauto using CIU_IsPreCtxRel. apply CTX_IsCtxRel.
  induction Γ; revgoals.
  - unfold CIU_open.
    intros.
    replace e1.[ξ] with e1.[mk_exp (ξ 0) /].[(fun n => n + 1) >>> ξ]; revgoals.
    { simpl.
      (* replace (ξ 0).[_] with (ξ 0).
      autosubst. *)
      replace ((fun n => n + 1) >>> ξ) with (upn 0 ((fun n => n + 1) >>> ξ)) by auto.
      rewrite escoped_ignores_sub.
        auto.
        1-2: admit.
    }
    replace e2.[ξ] with e2.[mk_exp (ξ 0) /].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      admit.
    }
    apply IHΓ.
    apply CTX_closed_under_substitution; auto; revgoals.
    + specialize (H0 0 ltac:(lia)). destruct (ξ 0); auto.
      ** simpl. replace e with (e.[idsubst]) by auto.
         apply -> subst_preserves_scope_val; eauto. intro. intros. inversion H1.
      ** inversion H0.
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
      * inversion H1. subst. destruct H2.
        
       
       
       
(*         replace (μeval_star e1 _ _)
          with (μeval_star (Seq e1 e) K A);
          revgoals.
        {
          run_μeval_star_for 1.
          auto.
        }
        replace (μeval_star e2 _ A)
          with (μeval_star (Seq e2 e) K A);
          revgoals.
        { run_μeval_star_for 1.
          auto.
        }
        inversion H1; subst.
        apply IHK; auto.
        apply HR'; auto.
        apply HR'; auto. *)
Admitted.

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

Definition equivalent_exps (e1 e2 : Exp) (R : Exp -> Exp -> Prop) : Prop :=
  forall v1, ⟨ [], e1 ⟩ -->* v1 -> (exists v2, ⟨ [], e2 ⟩ -->* v2 /\ R v1 v2).

Fixpoint equivalent_values (n : nat) (v1 v2 : Exp) : Prop :=
match n with
| 0 => True
| S n' =>
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => forall vals,
    length vals = length vl1 -> length vals = length vl2 ->
    equivalent_exps (b1.[list_subst vals idsubst]) (b2.[list_subst vals idsubst])
                    (equivalent_values n')
  | _, _ => False
  end
end.

Definition eq_exps (e1 e2 : Exp) := forall n, equivalent_exps e1 e2 (equivalent_values n).

Goal
  forall e1 e2, CTX 0 e1 e2 -> eq_exps e1 e2.
Proof.
  intros. intro. revert H. generalize dependent e2. generalize dependent e1.
  induction n; intros.
  * unfold equivalent_exps. intros. cbn. destruct H, H.
    apply ex_intro in H0. apply -> terminates_eq_terminates_sem in H0.
    apply (H1 CHole ltac:(constructor)) in H0. apply terminates_eq_terminates_sem in H0.
    destruct H0. exists x. split; auto.
  * unfold equivalent_exps. intros. cbn. destruct H, H.
    apply ex_intro in H0. apply -> terminates_eq_terminates_sem in H0.
Qed.

