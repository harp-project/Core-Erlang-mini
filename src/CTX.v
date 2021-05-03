Require Import LogRel.

Import ListNotations.

Definition Adequate (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall e1 e2,
    R [] e1 e2 ->
    forall v1 v2, equivalent_values v1 v2 -> (exists clock, eval clock e1 = Res v1) <-> 
                                             (exists clock, eval clock e2 = Res v2).

Definition IsReflexive (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e,
  EXP Γ ⊢ e -> R Γ e e.

Definition CompatibleFun (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ vl e1 e2,
    R (map inl vl ++ Γ) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl e2).

Definition CompatibleRecFun (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f vl e1 e2,
    R ((inr f :: map inl vl) ++ Γ) e1 e2 ->
    R Γ (ERecFun f vl e1) (ERecFun f vl e2).

Definition CompatibleApp (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f1 f2 vals1 vals2,
  Forall (fun e => EXP Γ ⊢ e) vals1 -> Forall (fun e => EXP Γ ⊢ e) vals2 ->
  EXP Γ ⊢ f1 -> EXP Γ ⊢ f2 ->
  R Γ f1 f2 -> Forall (fun '(e1, e2) => R Γ e1 e2) (combine vals1 vals2) ->
  R Γ (EApp f1 vals1) (EApp f2 vals2).

Definition CompatibleLet (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' x e2 e2',
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> EXP (inl x :: Γ) ⊢ e2 -> EXP (inl x :: Γ) ⊢ e2' ->
  R Γ e1 e1' -> R (inl x :: Γ) e2 e2' ->
  R Γ (ELet x e1 e2) (ELet x e1' e2').

Definition CompatibleLetRec (R : list VarFunId -> Exp -> Exp -> Prop) :=
  forall Γ f vl b1 b1' e2 e2',
  EXP (inr f :: map inl vl) ++ Γ ⊢ b1 -> EXP (inr f :: map inl vl) ++ Γ ⊢ b1' -> 
  EXP (inr f :: Γ) ⊢ e2 -> EXP (inr f :: Γ) ⊢ e2' ->
  R ((inr f :: map inl vl) ++ Γ) b1 b1' -> R (inr f :: Γ) e2 e2' ->
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

Inductive CTX :=
| CHole
| CFun      (vl : list Var) (e : CTX)
| CRecFun   (f : FunctionIdentifier) (vl : list Var) (e : CTX)
| CAppFun   (exp : CTX) (l : list Exp)
| CAppParam (exp : Exp) (l1 : list Exp) (c : CTX) (l2 : list Exp)  (* one of the middle ones is a ctx *)
| CLet1     (v : Var) (e1 : CTX) (e2 : Exp)
| CLet2     (v : Var) (e1 : Exp) (e2 : CTX)
| CLetRec1  (f : FunctionIdentifier) (vl : list Var) (b : CTX) (e : Exp)
| CLetRec2  (f : FunctionIdentifier) (vl : list Var) (b : Exp) (e : CTX)
| CPlus1     (e1 : CTX) (e2 : Exp)
| CPlus2     (e1 : Exp) (e2 : CTX)
| CIf1      (e1 : CTX) (e2 e3 : Exp)
| CIf2      (e1 : Exp) (e2 : CTX) (e3 : Exp)
| CIf3      (e1 e2 : Exp) (e3 : CTX).

Fixpoint plug (C : CTX) (p : Exp) :=
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

Fixpoint plugc (Where : CTX) (p : CTX) :=
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

Inductive EECtxScope (Γh : list VarFunId) : list VarFunId -> CTX -> Prop :=
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
with VECtxScope (Γh : list VarFunId) : list VarFunId -> CTX -> Prop :=
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


