Require Import LogRel.

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

Definition Adequate (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall e1 e2,
    R [] e1 e2 ->
    forall v1, (exists clock, eval clock e1 = Res v1) ->
         exists v2, (exists clock, eval clock e2 = Res v2) /\ equivalent_values v1 v2.

Definition IsReflexive (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e,
  EXP Γ ⊢ e -> R Γ e e.

Definition CompatibleFun (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ vl e1 e2,
    R (Γ ++ map inl vl) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl e2).

Definition CompatibleRecFun (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f vl e1 e2,
    R (Γ ++ (inr f :: map inl vl)) e1 e2 ->
    R Γ (ERecFun f vl e1) (ERecFun f vl e2).

Definition CompatibleApp (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f1 f2 vals1 vals2,
  Forall (fun e => EXP Γ ⊢ e) vals1 -> Forall (fun e => EXP Γ ⊢ e) vals2 ->
  EXP Γ ⊢ f1 -> EXP Γ ⊢ f2 ->
  R Γ f1 f2 -> Forall (fun '(e1, e2) => R Γ e1 e2) (combine vals1 vals2) ->
  R Γ (EApp f1 vals1) (EApp f2 vals2).

Definition CompatibleLet (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' x e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP (Γ ++ [inl x]) ⊢ e2 -> EXP (Γ ++ [inl x]) ⊢ e2' ->
  R Γ e1 e1' -> R (Γ ++ [inl x]) e2 e2' ->
  R Γ (ELet x e1 e2) (ELet x e1' e2').

Definition CompatibleLetRec (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f vl b1 b1' e2 e2',
  EXP Γ ++ (inr f :: map inl vl) ⊢ b1 -> EXP Γ ++ (inr f :: map inl vl) ⊢ b1' -> 
  EXP Γ ++ [inr f] ⊢ e2 -> EXP Γ ++ [inr f] ⊢ e2' ->
  R (Γ ++ (inr f :: map inl vl)) b1 b1' -> R (Γ ++ [inr f]) e2 e2' ->
  R Γ (ELetRec f vl b1 e2) (ELetRec f vl b1' e2').

Definition CompatiblePlus (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
  R Γ e1 e1' -> R Γ e2 e2' ->
  R Γ (EPlus e1 e2) (EPlus e1' e2').

Definition CompatibleIf (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2' e3 e3',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' -> EXP Γ ⊢ e3 -> EXP Γ ⊢ e3' -> (* is this needed? *)
  R Γ e1 e1' -> R Γ e2 e2' -> R Γ e3 e3' ->
  R Γ (EIf e1 e2 e3) (EIf e1' e2' e3').

Definition IsPreCtxRel (R : list VarFunId -> Exp -> Exp -> Prop) :=
  (forall Γ e1 e2, R Γ e1 e2 -> EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\ CompatibleRecFun R /\ CompatibleApp R /\ CompatibleLet R/\ CompatibleLetRec R /\
  CompatiblePlus R /\ CompatibleIf R.

Definition IsCtxRel (R : list VarFunId -> Exp -> Exp -> Prop) :=
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

Reserved Notation "'EECTX' Γh ⊢ C ;; Γ" (at level 60).
Reserved Notation "'VECTX' Γh ⊢ C ;; Γ" (at level 60).

Inductive EECtxScope (Γh : list VarFunId) : list VarFunId -> Ctx -> Prop :=
| CEScope_hole : (EECTX Γh ⊢ CHole ;; Γh)
| CEScope_App_f : forall Γ C exps,
    EECTX Γh ⊢ C ;; Γ -> 
    (Forall (fun v => EXP Γ ⊢ v) exps) ->
    EECTX Γh ⊢ CAppFun C exps ;; Γ
| CEScope_App_v : forall Γ f l1 l2 C,
    EXP Γ ⊢ f ->
    (Forall (fun v => EXP Γ ⊢ v) l1) -> (Forall (fun v => EXP Γ ⊢ v) l2) ->
    EECTX Γh ⊢ C ;; Γ -> 
    EECTX Γh ⊢ CAppParam f l1 C l2 ;; Γ
| CEScope_Let1 : forall Γ x C e2,
    EECTX Γh ⊢ C ;; Γ -> 
    EXP (Γ ++ [inl x]) ⊢ e2 ->
    EECTX Γh ⊢ CLet1 x C e2 ;; Γ
| CEScope_Let2 : forall Γ x e1 C,
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ C ;; (Γ ++ [inl x]) ->
    EECTX Γh ⊢ CLet2 x e1 C ;; Γ
| CEScope_LetRec1 : forall Γ f vl C e2,
    EECTX Γh ⊢ C ;; (Γ ++ (inr f :: map inl vl)) -> 
    EXP (Γ ++ [inr f]) ⊢ e2 ->
    EECTX Γh ⊢ CLetRec1 f vl C e2 ;; Γ
| CEScope_LetRec2 : forall Γ f vl e1 C,
    EXP Γ ++ (inr f :: map inl vl) ⊢ e1 ->
    EECTX Γh ⊢ C ;; (Γ ++ [inr f]) ->
    EECTX Γh ⊢ CLetRec2 f vl e1 C ;; Γ
| CEScope_Plus1 : forall Γ C e2,
    EECTX Γh ⊢ C ;; Γ -> 
    EXP Γ ⊢ e2 ->
    EECTX Γh ⊢ CPlus1 C e2 ;; Γ
| CEScope_Plus2 : forall Γ e1 C,
    EXP Γ ⊢ e1 ->
    EECTX Γh ⊢ C ;; Γ -> 
    EECTX Γh ⊢ CPlus2 e1 C ;; Γ
| CEScope_If1 : forall Γ C e2 e3,
    EECTX Γh ⊢ C ;; Γ -> 
    EXP Γ ⊢ e2 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CIf1 C e2 e3 ;; Γ
| CEScope_If2 : forall Γ C e1 e3,
    EECTX Γh ⊢ C ;; Γ -> 
    EXP Γ ⊢ e1 ->
    EXP Γ ⊢ e3 ->
    EECTX Γh ⊢ CIf2 e1 C e3 ;; Γ
| CEScope_If3 : forall Γ C e1 e2,
    EECTX Γh ⊢ C ;; Γ -> 
    EXP Γ ⊢ e1 ->
    EXP Γ ⊢ e2 ->
    EECTX Γh ⊢ CIf3 e1 e2 C ;; Γ
| CEScope_val : forall C Γ, VECTX Γh ⊢ C ;; Γ -> EECTX Γh ⊢ C ;; Γ
with VECtxScope (Γh : list VarFunId) : list VarFunId -> Ctx -> Prop :=
| CEScope_Fun : forall Γ vl C,
    EECTX Γh ⊢ C ;; (Γ ++ map inl vl) ->
    VECTX Γh ⊢ CFun vl C ;; Γ
| CEScope_RecFun : forall Γ f vl C,
    EECTX Γh ⊢ C ;; (Γ ++ (inr f :: map inl vl)) ->
    VECTX Γh ⊢ CRecFun f vl C ;; Γ
where
"'EECTX' Γh ⊢ C ;; Γ" := (EECtxScope Γh Γ C)
and
"'VECTX' Γh ⊢ C ;; Γ" := (VECtxScope Γh Γ C).

Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inversion H]
  end.

Lemma nth_possibilities {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.

Lemma nth_possibilities_alt {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2 /\ i >= length l1.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ;; Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e) /\
    (VECTX Γh ⊢ C ;; Γ ->
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
    (EECTX Γ' ⊢ Couter ;; Γ ->
     EECTX Γh ⊢ Cinner ;; Γ' ->
     EECTX Γh ⊢ plugc Couter Cinner ;; Γ) /\
    (VECTX Γ' ⊢ Couter ;; Γ ->
     EECTX Γh ⊢ Cinner ;; Γ' ->
     VECTX Γh ⊢ plugc Couter Cinner ;; Γ).
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

Definition CTX (Γ : list VarFunId) (e1 e2 : Exp) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ;; [] -> forall v1,
      (exists clock, eval clock (plug C e1) = Res v1) -> 
      exists v2, (exists clock, eval clock (plug C e2) = Res v2) /\ equivalent_values v1 v2).

Lemma IsReflexiveList : forall R' l Γ',
  IsReflexive R' -> Forall (fun v : Exp => EXP Γ' ⊢ v) l ->
  Forall (fun '(e0, e3) => R' Γ' e0 e3) (combine l l).
Proof.
  induction l; intros; constructor.
  * apply H. inversion H0. auto.
  * inversion H0. apply IHl; auto.
Qed.

Lemma CTX_bigger : forall R' : list VarFunId -> Exp -> Exp -> Prop,
    IsPreCtxRel R' -> forall (Γ : list VarFunId) (e1 e2 : Exp), R' Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros R' HR.
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RRecFun [RApp [RLet [RLetRec [RPlus  RIf ] ] ] ] ] ] ] ] ] ].
  unfold CTX.
  intros.
  destruct (Rscope _ _ _ H) as [Hscope_e1 Hscope_e2].
  intuition idtac;
    try solve [apply Rscope in H; intuition idtac];
    apply Radequate.
  assert (forall Γ', EECTX Γ ⊢ C ;; Γ' -> 
                     R' Γ' (plug C e1) (plug C e2)).
  { clear H0.
    induction C;
      intros;
      inversion H0;
      subst;
      cbn;
      try solve_inversion;
      auto.
    - apply RFun.
      apply IHC.
      inversion H1; auto.
    - apply RRecFun.
      apply IHC.
      inversion H1; auto.
    - apply RApp; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + apply IsReflexiveList; auto.
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
      + rewrite indexed_to_forall. intros.
        rewrite combine_nth. 2: repeat rewrite app_length; simpl; lia.
        rewrite combine_length in H1.
        assert ((length (l1 ++ plug C e1 :: l2)) = length (l1 ++ plug C e2 :: l2)).
        { repeat rewrite app_length. simpl. lia. }
        rewrite H2 in H1. rewrite Nat.min_id in H1.
        epose (nth_possibilities_alt _ _ _ _ H1). destruct o.
        ** destruct H3. rewrite H3. rewrite app_nth1; auto.
           apply Rrefl. rewrite Forall_nth in H7. apply H7; auto.
        ** destruct H3. destruct H4. rewrite H3. rewrite app_nth2; auto.
           remember (i - length l1) as i'. destruct i'.
           -- simpl. apply IHC. auto.
           -- simpl. apply Rrefl. rewrite Forall_nth in H8. apply H8. rewrite Heqi' in *. simpl in H4. lia.
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
  apply H1.
  auto. Grab Existential Variables. exact (ELit 0).
Qed.

Lemma CTX_refl Γ e : EXP Γ ⊢ e -> CTX Γ e e.
Proof.
  unfold CTX. intros. split; auto.
  intros. intuition. destruct H1. exists v1. split. eexists. eauto.
  exists 0. eapply Vrel_Fundamental_closed.
  
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
    + eapply (H2 CHole); eauto.
      constructor.
    + eapply (H2 CHole); eauto.
      constructor.
  * unfold IsReflexive.
    intros.
    unfold CTX.
    
  - unfold Transitive.
    intros.
    unfold CTX in *.
    intuition idtac.
    eapply Rbar_le_trans; firstorder.
  - unfold CompatibleFun.
    intros.
    unfold CTX in *.
    intuition auto.
    specialize (H1 (plugc C (Ctx_Fun Ctx_hole)) A).
    repeat rewrite <- plug_assoc in H1.
    cbn in H1.
    apply H1.
    eapply plugc_preserves_scope_exp; eauto.
    repeat constructor.
  - unfold CompatibleApp.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (App (Var 0) (rename (+1) v1))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      constructor.
      auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; asimpl; auto.
    }
    specialize (H6 _ A H10).
    repeat rewrite <- plug_assoc in H6.
    cbn in H6.
    assert (forall f1 v1,
               VAL Γ ⊢ f1 ->
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (App f1 v1)) Knil A =
                μeval_star (plug C (Seq f1 (App (Var 0) (rename (+1) v1)))) Knil A))
      as HApp_Seq_f.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      reflexivity.
      constructor; auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; cbn; auto.
    }
    assert (forall f1 v1,
               VAL Γ ⊢ f1 ->
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (App f1 v1)) Knil A =
                μeval_star (plug C (Seq v1 (App (rename (+1) f1) (Var 0)))) Knil A))
      as HApp_Seq_v.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      reflexivity.
      constructor; auto.
      apply -> ren_preserves_scope_val; eauto.
      unfold RenScoped.
      intros; cbn; auto.
    }
    rewrite HApp_Seq_f; auto.
    eapply Rbar_le_trans.
    apply H6.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (App (rename (+1) f2) (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        intros; asimpl; auto.
      - constructor.
        auto.
    }
    specialize (H7 _ A H11).
    repeat rewrite <- plug_assoc in H7.
    rewrite HApp_Seq_v; auto.
    eapply Rbar_le_trans; revgoals.
    cbn in H7.
    apply H7.
    rewrite <- HApp_Seq_v; auto.
    rewrite <- HApp_Seq_f; auto.
  - unfold CompatibleOp1.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op1 o (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      constructor.
      auto.
    }
    specialize (H3 _ A H5).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Op1 o v1)) Knil A =
                μeval_star (plug C (Seq v1 (Op1 o (Var 0)))) Knil A))
      as HApp_Op1.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      constructor.
      auto.
    }
    rewrite HApp_Op1; auto.
    eapply Rbar_le_trans.
    apply H3.
    rewrite HApp_Op1; auto.
  - unfold CompatibleOp2.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op2 o (Var 0) (rename (+1) v1'))) ∷ 0).
    { eapply plugc_preserves_scope_exp;
        eauto;
        repeat (constructor; auto 1).
      apply -> ren_preserves_scope_val;
        eauto.
      unfold RenScoped.
      cbn.
      auto.
    }
    specialize (H6 _ A H10).
    repeat rewrite <- plug_assoc in H6.
    cbn in H6.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Op2 o v1 v1')) Knil A =
                μeval_star (plug C (Seq v1 (Op2 o (Var 0) (rename (+1) v1')))) Knil A))
      as HApp_Op2_1.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - auto.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        cbn.
        auto.
    }
    assert (forall v1',
               VAL Γ ⊢ v1' ->
               (μeval_star (plug C (Op2 o v2 v1')) Knil A =
                μeval_star (plug C (Seq v1' (Op2 o (rename (+1) v2) (Var 0)))) Knil A))
      as HApp_Op2_2.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        cbn.
        auto.
      - auto.
    }
    rewrite HApp_Op2_1; auto.
    eapply Rbar_le_trans.
    apply H6.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Op2 o (rename (+1) v2) (Var 0))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      constructor.
      - apply -> ren_preserves_scope_val; eauto.
        unfold RenScoped.
        intros; asimpl; auto.
      - constructor.
        auto.
    }
    specialize (H7 _ A H11).
    repeat rewrite <- plug_assoc in H7.
    rewrite HApp_Op2_2; auto.
    eapply Rbar_le_trans; revgoals.
    cbn in H7.
    apply H7.
    rewrite <- HApp_Op2_2; auto.
    rewrite <- HApp_Op2_1; auto.
  - unfold CompatibleCond.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ plugc C (Ctx_Cond_t v1 Ctx_hole ef1) ∷ 0) as HCtx_t.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX Γ ⊢ plugc C (Ctx_Cond_f v1 et2 Ctx_hole) ∷ 0) as HCtx_f.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    specialize (H10 _ A HCtx_t).
    repeat rewrite <- plug_assoc in H10.
    cbn in H10.
    eapply Rbar_le_trans.
    apply H10.
    specialize (H11 _ A HCtx_f).
    repeat rewrite <- plug_assoc in H11.
    cbn in H11.
    eapply Rbar_le_trans.
    apply H11.
    assert (EECTX Γ ⊢ plugc C (Ctx_Seq_x Ctx_hole (Cond (Var 0) (rename (+1) et2) (rename (+1) ef2))) ∷ 0) as HCtx_p.
    { eapply plugc_preserves_scope_exp;
        eauto.
      constructor.
      constructor.
      constructor.
      + constructor.
        auto.
      + apply -> ren_preserves_scope_exp;
          eauto.
        unfold RenScoped.
        cbn.
        auto 1.
      + apply -> ren_preserves_scope_exp;
          eauto.
        unfold RenScoped.
        cbn.
        auto 1.
    }
    specialize (H9 _ A HCtx_p).
    repeat rewrite <- plug_assoc in H9.
    cbn in H9.
    assert (forall vp,
               VAL Γ ⊢ vp ->
               (μeval_star (plug C (Cond vp et2 ef2)) Knil A =
                μeval_star (plug C (Seq vp (Cond (Var 0) (rename (+1) et2) (rename (+1) ef2)))) Knil A))
      as HSeq_Cond_p.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      asimpl.
      auto.
      constructor.
      - auto.
      - apply -> ren_preserves_scope_exp; eauto.
        unfold RenScoped.
        cbn.
        auto 1.
      - apply -> ren_preserves_scope_exp; eauto.
        unfold RenScoped.
        cbn.
        auto 1.
    }
    rewrite HSeq_Cond_p; auto.
    eapply Rbar_le_trans.
    apply H9.
    rewrite <- HSeq_Cond_p; auto.
  - unfold CompatibleSeq.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ (plugc C (Ctx_Seq_x Ctx_hole b1)) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      auto.
    }
    specialize (H2 _ A H6).
    repeat rewrite <- plug_assoc in H2.
    cbn in H2.
    eapply Rbar_le_trans.
    eapply H2.
    assert (EECTX S Γ ⊢ (plugc C (Ctx_Seq_b x2 Ctx_hole)) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      auto.
      constructor.
    }
    specialize (H3 _ A H7).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    apply H3.
  - unfold CompatibleFactor.
    intros.
    unfold CTX in *.
    intuition auto.
    assert (EECTX Γ ⊢ (plugc C (Ctx_Seq_x Ctx_hole (Factor (Var 0)))) ∷ 0).
    { eapply plugc_preserves_scope_exp; eauto.
      constructor.
      constructor.
      auto.
    }
    specialize (H3 _ A H5).
    repeat rewrite <- plug_assoc in H3.
    cbn in H3.
    assert (forall v1,
               VAL Γ ⊢ v1 ->
               (μeval_star (plug C (Factor v1)) Knil A =
                μeval_star (plug C (Seq v1 (Factor (Var 0)))) Knil A))
      as HFactor_Seq.
    { intros.
      erewrite use_Seq_instead; eauto 2.
      auto.
    }
    rewrite HFactor_Seq; auto.
    rewrite HFactor_Seq; auto.
Qed.

