Require Import ExpSemantics.

Import ListNotations.

Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_rt fs e fs' e') (at level 50).
Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e') (at level 50).

Inductive Context : Set :=
| CBox
| CLit    (l : Z)
| CVar    (v : Var)
| CFunId  (f : FunctionIdentifier)
| CFun    (vl : list Var) (c : Context)
| CRecFun (f : FunctionIdentifier) (vl : list Var) (c : Context)
| CApp    (c : Context)     (l : list Context)
| CLet    (v : Var) (c1 c2 : Context)
| CLetRec (f : FunctionIdentifier) (vl : list Var) (c1 c2 : Context)
| CPlus   (c1 c2 : Context)
| CIf (c1 c2 c3 : Context).

Fixpoint fill_boxes (e : Exp) (C : Context) : Exp :=
match C with
 | CBox => e
 | CLit l => ELit l
 | CVar v => EVar v
 | CFunId f => EFunId f
 | CFun vl c => EFun vl (fill_boxes e c)
 | CRecFun f vl c => ERecFun f vl (fill_boxes e c)
 | CApp c l => EApp (fill_boxes e c) (map (fill_boxes e) l)
 | CLet v c1 c2 => ELet v (fill_boxes e c1) (fill_boxes e c2)
 | CLetRec f vl c1 c2 => ELetRec f vl (fill_boxes e c1) (fill_boxes e c2)
 | CPlus c1 c2 => EPlus (fill_boxes e c1) (fill_boxes e c2)
 | CIf c1 c2 c3 => EIf (fill_boxes e c1) (fill_boxes e c2) (fill_boxes e c3)
end.

Notation "C [[ e ]]" := (fill_boxes e C) (at level 30).

Compute (CBox) [[ ELit 1 ]].

(*
Inductive value_equivalent : Exp -> Exp -> Prop :=
| vrefl v : is_value v -> value_equivalent v v
| vclos : forall v1 v2, is_value v1 -> is_value v2 ->
   (forall vals fs, | fs, EApp (EFun vl e) vals | -->* |fs, v1 |) .

Definition ctx_preorder (e1 e2 : Exp) : Prop :=
  forall (C : Context) (* (fs : FrameStack)  *) (v1 v2 : Exp),
  is_value v1 -> is_value v2 -> value_equivalent v1 v2
->
  | [], C[[e1]] | -->* | [], v1 | -> | [], C[[e2]] | -->* | [], v2 |
.

Definition ctx_equivalent (e1 e2 : Exp) : Prop :=
  ctx_preorder e1 e2 /\ ctx_preorder e2 e1
.

Lemma ctx_preorder_refl :
  forall e, ctx_preorder e e.
Proof. firstorder. Qed.

Lemma ctx_preorder_trans :
  forall e1 e2 e3, ctx_preorder e1 e2 -> ctx_preorder e2 e3
->
  ctx_preorder e1 e3.
Proof. firstorder. Qed.

Lemma ctx_eq_refl :
  forall e, ctx_equivalent e e.
Proof. firstorder. Qed.

Lemma ctx_eq_sym :
  forall e1 e2, ctx_equivalent e1 e2 -> ctx_equivalent e2 e1.
Proof. firstorder. Qed.

Lemma ctx_eq_trans :
  forall e1 e2 e3,
  ctx_equivalent e1 e2 -> ctx_equivalent e2 e3
->
  ctx_equivalent e1 e3.
Proof. firstorder. Qed.

Theorem relations_simulation :
  exists R : Exp -> Exp -> Prop,
  forall (e1 e2 : Exp) (v1 v2 : Exp),
  (forall fs : FrameStack, | fs, e1 | -->* | fs, v1 |) -> is_value v1 ->
  (forall fs : FrameStack, | fs, e2 | -->* | fs, v2 |) -> is_value v2 ->
  R v1 v2 
->
  R e1 e2.
Proof.

Admitted.*)