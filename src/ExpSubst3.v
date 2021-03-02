Require Export ExpSyntax.
Require Import ccs.Trans_Sys.
Export PeanoNat.
Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FSets.FMapFacts.

Import ListNotations.

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

Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.

Section correct_ctx_ind.

  Variables
    (P : Context -> Prop)(Q : list Context -> Prop).

  Hypotheses
   (H : P CBox)
   (H0 : forall (l : Z), P (CLit l))
   (H1 : forall (v : Var), P (CVar v))
   (H2 : forall (f : FunctionIdentifier), P (CFunId f))
   (H3 : forall (vl : list Var) (e : Context), P e -> P (CFun vl e))
   (H4 : forall (f : FunctionIdentifier) (vl : list Var) (e : Context), P e -> P (CRecFun f vl e))
   (H5 : forall (e : Context), P e -> forall (el : list Context), Q el 
       -> P (CApp e el))
   (H6 : forall (v : Var) (e1 : Context), P e1 -> forall e2 : Context, P e2 
       -> P (CLet v e1 e2))
   (H7 : forall (f : FunctionIdentifier) (vl : list Var) (b : Context), P b -> forall e : Context, P e 
       -> P (CLetRec f vl b e))
   (H8 : forall (e1 : Context), P e1 -> forall e2 : Context, P e2 
       -> P (CPlus e1 e2))
   (H9 : forall (e1 : Context), P e1 -> forall e2 : Context, P e2 -> forall e3 : Context, P e3
       -> P (CIf e1 e2 e3))
   (H' : forall v : Context, P v -> forall l:list Context, Q l -> Q (v :: l))
   (H1' : Q []).

  Fixpoint Context_ind2 (e : Context) : P e :=
  match e as x return P x with
  | CBox => H
  | CLit l => H0 l
  | CVar s => H1 s
  | CFunId f => H2 f
  | CFun vl e => H3 vl e (Context_ind2 e)
  | CRecFun f vl e => H4 f vl e (Context_ind2 e)
  | CApp e el => H5 e (Context_ind2 e) el ((fix l_ind (l':list Context) : Q l' :=
                                         match l' as x return Q x with
                                         | [] => H1'
                                         | v::xs => H' v (Context_ind2 v) xs (l_ind xs)
                                         end) el)
  | CLet v e1 e2 => H6 v e1 (Context_ind2 e1) e2 (Context_ind2 e2)
  | CLetRec f vl b e => H7 f vl b (Context_ind2 b) e (Context_ind2 e)
  | CPlus e1 e2 => H8 e1 (Context_ind2 e1) e2 (Context_ind2 e2)
  | CIf e1 e2 e3 => H9 e1 (Context_ind2 e1) e2 (Context_ind2 e2) e3 (Context_ind2 e3)
  end.

End correct_ctx_ind.

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

Inductive is_value : Exp -> Prop :=
| ELit_val : forall l, is_value (ELit l)
| EFun_val : forall vl e, is_value (EFun vl e)
| ERecFun_val : forall f vl e, is_value (ERecFun f vl e).

Inductive ResultType {T : Set} : Set :=
| Timeout
| Fail
| Res (v : T)
.

(* The equality of function signatures *)
Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
match v1, v2 with
| (fid1, num1), (fid2, num2) => String.eqb fid1 fid2 && Nat.eqb num1 num2
end.

(* Extended equality between functions and vars *)
Definition var_funid_eqb (v1 v2 : Var + FunctionIdentifier) : bool :=
match v1, v2 with
| inl s1, inl s2 => String.eqb s1 s2
| inr f1, inr f2 => funid_eqb f1 f2
| _, _ => false
end.

Fixpoint varsubst (v' : Var) (what wher : Exp) : Exp :=
match wher with
 | ELit l => wher
 | EVar v => if String.eqb v v' then what else EVar v
 | EFunId f => wher
 | EFun vl e => if in_list v' vl then EFun vl e else EFun vl (varsubst v' what e)
 | ERecFun f vl e => if in_list v' vl then ERecFun f vl e else ERecFun f vl (varsubst v' what e)
 | EApp exp l => EApp (varsubst v' what exp) (map (varsubst v' what) l)
 | ELet v e1 e2 => if String.eqb v v' then ELet v (varsubst v' what e1) e2
                               else ELet v (varsubst v' what e1) (varsubst v' what e2)
 | ELetRec f vl b e => if in_list v' vl then ELetRec f vl b (varsubst v' what e) 
                                        else ELetRec f vl (varsubst v' what b) (varsubst v' what e)
 | EPlus e1 e2 => EPlus (varsubst v' what e1) (varsubst v' what e2)
 | EIf e1 e2 e3 => EIf (varsubst v' what e1) (varsubst v' what e2) (varsubst v' what e3) 
end.

Fixpoint funsubst (f' : FunctionIdentifier) (what wher : Exp) : Exp :=
match wher with
 | ELit l => wher
 | EVar v => EVar v
 | EFunId f => if funid_eqb f f' then what else wher
 | EFun vl e => EFun vl (funsubst f' what e)
 | ERecFun f vl e => ERecFun f vl (funsubst f' what e)
 | EApp exp l => EApp (funsubst f' what exp) (map (funsubst f' what) l)
 | ELet v e1 e2 => ELet v (funsubst f' what e1) (funsubst f' what e2)
 | ELetRec f vl b e => if funid_eqb f f'
                       then ELetRec f vl b e
                       else ELetRec f vl (funsubst f' what b) (funsubst f' what e)
 | EPlus e1 e2 => EPlus (funsubst f' what e1) (funsubst f' what e2)
 | EIf e1 e2 e3 => EIf (funsubst f' what e1) (funsubst f' what e2) (funsubst f' what e3)
end.


Definition varsubst_list (l : list Var) (es : list Exp) (e : Exp) : Exp :=
  fold_right (fun '(v, val) acc => varsubst v val acc) e (combine l es).

(** Closing substitution *)
Definition subst (v' : VarFunId) (what wher : Exp) (p : is_value what) : Exp :=
  match v' with
  | inl v => varsubst v what wher
  | inr f => funsubst f what wher
  end
.

Inductive list_forall {A : Type} (P : A -> Prop) : list A -> Prop :=
| forall_nil : list_forall P []
| forall_cons x xs : P x -> list_forall P xs -> list_forall P (x::xs).



Reserved Notation "e -[ t ]-> e'" (at level 50).
Inductive labelled_transitions : Exp -> unit -> Exp -> Prop :=
| eval_lit l : ELit l -[ tt ]-> ELit l
| eval_fun vl b : EFun vl b -[tt]-> EFun vl b
| eval_recfun f vl b : ERecFun f vl b -[tt]-> ERecFun f vl b

| eval_let_1 v e1 e2 e1' :
  ~is_value e1 -> e1 -[tt]-> e1' ->
  ELet v e1 e2 -[tt]-> ELet v e1' e2
| eval_let_2 v e1 e2 :
  is_value e1 ->
  ELet v e1 e2 -[tt]-> varsubst v e1 e2

| eval_letrec f vl b e :
  ELetRec f vl b e -[tt]-> funsubst f (ERecFun f vl b) e

(* TODO: EApp *)

| eval_plus_1 e1 e2 e1' :
  ~is_value e1 -> e1 -[tt]-> e1' ->
  EPlus e1 e2 -[tt]-> EPlus e1' e2
| eval_plus_2 e1 e2 e2' :
  is_value e1 -> ~is_value e2 -> e2 -[tt]-> e2' ->
  EPlus e1 e2 -[tt]-> EPlus e1 e2'
| eval_plus_3 l1 l2 :
  EPlus (ELit l1) (ELit l2) -[tt]-> ELit (l1 + l2)


| eval_if_1 e1 e2 e3 e1' :
  ~ is_value e1 -> e1 -[tt]-> e1' ->
  EIf e1 e2 e3 -[tt]-> EIf e1' e2 e3
| eval_if_true e2 e3 :
  EIf (ELit 0) e2 e3 -[tt]-> e2
| eval_if_false e1 e2 e3 :
  is_value e1 -> e1 <> ELit 0 ->
  EIf e1 e2 e3 -[tt]-> e3

where "e -[ t ]-> e'" := (labelled_transitions e t e')
.

Definition my_eq := (obs_eq Exp unit) tt labelled_transitions.

Goal my_eq (ELit 1) (EPlus (EPlus (ELit 0) (ELit 0)) (ELit 1)).
Proof.
  constructor.
  * intros. inversion H. subst. exists (EPlus (ELit 0) (ELit 1)). split.
    - constructor. apply eval_plus_1. intro. inversion H0. constructor.
    - constructor.
      + intros. inversion H0. subst. exists (ELit 1). split.
        ** constructor. constructor.
        ** apply refl_weak_eq.
      + intros. inversion H0; subst.
        ** exfalso. eapply H3. constructor.
        ** exfalso. eapply H4. constructor.
        ** exists (ELit 1). split. constructor. apply refl_weak_eq.
  * intros. inversion H; subst.
    - 
Qed.
