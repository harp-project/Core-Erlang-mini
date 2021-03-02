
From Coq Require Export ZArith.BinInt.
Require Export ExpEnv.
From Coq Require Export Lists.List.

Import ListNotations.

(* Inductive Literal : Set :=
| Atom (s: string)
| Integer (x : Z). *)

Definition Var : Set := string.

Definition FunctionIdentifier : Set := string * nat.

Inductive Exp : Set :=
| ELit    (l : Z)
| EVar    (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun    (vl : list Var) (e : Exp)
| ERecFun (f : FunctionIdentifier) (vl : list Var) (e : Exp) (** This is not a valid expression, letrec reduces to this *)
| EApp    (exp : Exp)     (l : list Exp)
| ELet    (v : Var) (e1 e2 : Exp)
| ELetRec (f : FunctionIdentifier) (vl : list Var) (b e : Exp)
(** Techical helpers: simplified bif: plus, simplified case: if *)
| EPlus   (e1 e2 : Exp)
| EIf (e1 e2 e3 : Exp).

Section correct_exp_ind.

  Variables
    (P : Exp -> Prop)(Q : list Exp -> Prop).

  Hypotheses
   (H0 : forall (l : Z), P (ELit l))
   (H1 : forall (v : Var), P (EVar v))
   (H2 : forall (f : FunctionIdentifier), P (EFunId f))
   (H3 : forall (vl : list Var) (e : Exp), P e -> P (EFun vl e))
   (H4 : forall (f : FunctionIdentifier) (vl : list Var) (e : Exp), P e -> P (ERecFun f vl e))
   (H5 : forall (e : Exp), P e -> forall (el : list Exp), Q el 
       -> P (EApp e el))
   (H6 : forall (v : Var) (e1 : Exp), P e1 -> forall e2 : Exp, P e2 
       -> P (ELet v e1 e2))
   (H7 : forall (f : FunctionIdentifier) (vl : list Var) (b : Exp), P b -> forall e : Exp, P e 
       -> P (ELetRec f vl b e))
   (H8 : forall (e1 : Exp), P e1 -> forall e2 : Exp, P e2 
       -> P (EPlus e1 e2))
   (H9 : forall (e1 : Exp), P e1 -> forall e2 : Exp, P e2 -> forall e3 : Exp, P e3
       -> P (EIf e1 e2 e3))
   (H' : forall v : Exp, P v -> forall l:list Exp, Q l -> Q (v :: l))
   (H1' : Q []).

  Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | ELit l => H0 l
  | EVar s => H1 s
  | EFunId f => H2 f
  | EFun vl e => H3 vl e (Exp_ind2 e)
  | ERecFun f vl e => H4 f vl e (Exp_ind2 e)
  | EApp e el => H5 e (Exp_ind2 e) el ((fix l_ind (l':list Exp) : Q l' :=
                                         match l' as x return Q x with
                                         | [] => H1'
                                         | v::xs => H' v (Exp_ind2 v) xs (l_ind xs)
                                         end) el)
  | ELet v e1 e2 => H6 v e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ELetRec f vl b e => H7 f vl b (Exp_ind2 b) e (Exp_ind2 e)
  | EPlus e1 e2 => H8 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | EIf e1 e2 e3 => H9 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) e3 (Exp_ind2 e3)
  end.

End correct_exp_ind.

Definition XVar : Var := "X"%string.
Definition YVar : Var := "Y"%string.
Definition ZVar : Var := "Z"%string.

Definition F0 : FunctionIdentifier := ("f"%string, 0).
Definition F1 : FunctionIdentifier := ("f"%string, 1).

Definition inc (n : Z) := ELet XVar (ELit n) (EPlus (EVar XVar) (ELit 1)).
Definition sum (n : Z) := ELetRec F1 [XVar] (EIf (EVar XVar) (EVar XVar) (
                                            (EPlus (EVar XVar)
                                            (EApp (EFunId F1) [EPlus (EVar XVar) (ELit (-1))]))))
                        (EApp (EFunId F1) [ELit n]).
Definition simplefun (n : Z) := ELet XVar (EFun [] (ELit n)) (EApp (EVar XVar) []).
Definition simplefun2 (n m : Z) := EApp (EFun [XVar; YVar] (EPlus (EVar XVar) (EVar YVar))) [ELit n; ELit m].

Fixpoint in_list (v : Var) (l : list Var) : bool :=
match l with
| [] => false
| x::xs => if eqb v x then true else in_list v xs
end.

Fixpoint varsubst (v' : Var) (what wher : Exp) : Exp :=
match wher with
 | ELit l => wher
 | EVar v => if eqb v v' then what else EVar v
 | EFunId f => wher
 | EFun vl e => wher
 | ERecFun f vl e => wher
 | EApp exp l => EApp (varsubst v' what exp) (map (varsubst v' what) l)
 | ELet v e1 e2 => if eqb v v' then ELet v (varsubst v' what e1) e2
                               else ELet v (varsubst v' what e1) (varsubst v' what e2)
 | ELetRec f vl b e => if in_list v' vl then ELetRec f vl b (varsubst v' what e) 
                                        else ELetRec f vl (varsubst v' what b) (varsubst v' what e)
 | EPlus e1 e2 => EPlus (varsubst v' what e1) (varsubst v' what e2)
 | EIf e1 e2 e3 => EIf (varsubst v' what e1) (varsubst v' what e2) (varsubst v' what e3) 
end.

Definition varsubst_list (l : list Var) (es : list Exp) (e : Exp) : Exp :=
  fold_right (fun '(v, val) acc => varsubst v val acc) e (combine l es).

Fixpoint funsubst (f' : FunctionIdentifier) (what wher : Exp) : Exp :=
match wher with
 | ELit l => wher
 | EVar v => EVar v
 | EFunId f => if andb (eqb (fst f) (fst f')) (Nat.eqb (snd f) (snd f')) then what else wher
 | EFun vl e => wher
 | ERecFun f vl e => wher
 | EApp exp l => EApp (funsubst f' what exp) (map (funsubst f' what) l)
 | ELet v e1 e2 => ELet v (funsubst f' what e1) (funsubst f' what e2)
 | ELetRec f vl b e => if andb (eqb (fst f) (fst f')) (Nat.eqb (snd f) (snd f'))
                       then ELetRec f vl b e
                       else ELetRec f vl (funsubst f' what b) (funsubst f' what e)
 | EPlus e1 e2 => EPlus (funsubst f' what e1) (funsubst f' what e2)
 | EIf e1 e2 e3 => EIf (funsubst f' what e1) (funsubst f' what e2) (funsubst f' what e3)
end.
