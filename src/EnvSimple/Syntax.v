From CoreErlang Require Export SyntaxBasics.
From stdpp Require Export base list.

(** The syntax of expressions: *)
Inductive Exp : Set :=
| EFun    (vl : nat) (e : Exp)
| EApp    (exp : Exp)     (l : list Exp)
| ELet    (e1 e2 : Exp)
| ECase (e : Exp) (p : Pat) (e1 e2 : Exp)
| ECons (e1 e2 : Exp)
| EBIF (e : Exp) (l : list Exp)
| EVar    (n : nat)
| ELit (l : Lit)
| EPid (p : PID)
| ENil.

Inductive Val : Set :=
| VLit    (l : Lit)
| VPid    (p : PID)
(** Variables and function identifiers are just indices.
    TODO: In the future, function identifiers should include the arity too!
*)
| VNil
(** Recursive data structures which are values: *)
| VCons (e1 e2 : Val)
| VClos (Γ : list Val) (vl : nat) (e : Exp).

Declare Scope env_simple_scope.
Delimit Scope env_simple_scope with envs.

Section correct_ind_exp.

Variables (P : Exp -> Prop)
          (Q : list Exp -> Prop).

Hypotheses
  (HExp_Fun : forall (vl : nat) (e : Exp), P e -> P (EFun vl e))
  (HExp_App : forall (e : Exp), P e -> forall (el : list Exp), Q el -> P (EApp e el))
  (HExp_Let : forall (e1 e2 : Exp), P e1 -> P e2 -> P (ELet e1 e2))
  (HExp_Case : forall (e : Exp) (p : Pat) (e1 e2 : Exp), P e -> P e1 -> P e2 -> P (ECase e p e1 e2))
  (HExp_Cons : forall (e1 e2 : Exp), P e1 -> P e2 -> P (ECons e1 e2))
  (HExp_BIF : forall (e : Exp), P e -> forall (l : list Exp), Q l -> P (EBIF e l))
  (HExp_Var : forall (n : nat), P (EVar n))
  (HExp_Lit : forall (l : Lit), P (ELit l))
  (HExp_Pid : forall (p : PID), P (EPid p))
  (HExp_Nil : P ENil)

  (HQ_nil : Q [])
  (HQ_cons : forall (e : Exp), P e -> forall (l : list Exp), Q l -> Q (e :: l)).

Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | EFun vl e => HExp_Fun vl e (Exp_ind2 e)
  | EApp e el => HExp_App e (Exp_ind2 e) el (
      (fix Exp_list_ind (l : list Exp) : Q l :=
         match l as x return Q x with
         | [] => HQ_nil
         | e :: xs => HQ_cons e (Exp_ind2 e) xs (Exp_list_ind xs)
         end) el)
  | ELet e1 e2 => HExp_Let e1 e2 (Exp_ind2 e1) (Exp_ind2 e2)
  | ECase e p e1 e2 => HExp_Case e p e1 e2 (Exp_ind2 e) (Exp_ind2 e1) (Exp_ind2 e2)
  | ECons e1 e2 => HExp_Cons e1 e2 (Exp_ind2 e1) (Exp_ind2 e2)
  | EBIF e l => HExp_BIF e (Exp_ind2 e) l (
      (fix Exp_list_ind (l : list Exp) : Q l :=
         match l as x return Q x with
         | [] => HQ_nil
         | e :: xs => HQ_cons e (Exp_ind2 e) xs (Exp_list_ind xs)
         end) l)
  | EVar n => HExp_Var n
  | ELit l => HExp_Lit l
  | EPid p => HExp_Pid p
  | ENil => HExp_Nil
  end.

End correct_ind_exp.

Section correct_ind_val.

Variables (PV : Val -> Prop)
          (R : list Val -> Prop).

Hypotheses
  (HVal_Lit : forall (l : Lit), PV (VLit l))
  (HVal_Pid : forall (n : nat), PV (VPid n))
  (HVal_Nil : PV VNil)
  (HVal_Cons : forall (v1 v2 : Val), PV v1 -> PV v2 -> PV (VCons v1 v2))
  (HVal_Clos : forall (Gamma : list Val) (vl : nat) (e : Exp), R Gamma -> PV (VClos Gamma vl e))

  (HR_nil : R [])
  (HR_cons : forall (v : Val), PV v -> forall (l : list Val), R l -> R (v :: l)).

Fixpoint Val_ind2 (v : Val) : PV v :=
  match v as x return PV x with
  | VLit l => HVal_Lit l
  | VPid p => HVal_Pid p
  | VNil => HVal_Nil
  | VCons v1 v2 => HVal_Cons v1 v2 (Val_ind2 v1) (Val_ind2 v2)
  | VClos Gamma vl e => HVal_Clos Gamma vl e (
      (fix Val_list_ind (l : list Val) : R l :=
         match l as x return R x with
         | [] => HR_nil
         | v :: xs => HR_cons v (Val_ind2 v) xs (Val_list_ind xs)
         end) Gamma)
  end.

End correct_ind_val.

Fixpoint match_pattern (p : Pat) (e : Val) : option (list Val) :=
match p with
| PVar => Some [e]
| PPid x => match e with
            | VPid p => if Nat.eqb p x then Some [] else None
            | _      => None
            end
| PNil => match e with
          | VNil => Some []
          | _    => None
          end
| PLit l0 => match e with
             | VLit l => if lit_eqb l l0 then Some [] else None
             | _      => None
             end
| PCons p1 p2 => 
  match e with
  | VCons v1 v2 =>
    match match_pattern p1 v1, match_pattern p2 v2 with
    | Some l1, Some l2 => Some (l1 ++ l2)
    | _      , _       => None
    end
  | _           => None
  end
end.

Fixpoint pat_vars (p : Pat) : nat :=
match p with
 | PLit _ => 0
 | PPid _ => 0
 | PVar => 1
 | PNil => 0
 | PCons p1 p2 => pat_vars p1 + pat_vars p2
end.

Lemma match_pattern_length : forall p v l,
  match_pattern p v = Some l -> pat_vars p = length l.
Proof.
  induction p; intros.
  * simpl in *. destruct v; inversion H. break_match_hyp; now inversion H.
  * simpl in *. destruct v; inversion H. break_match_hyp; now inversion H.
  * simpl in *. destruct v; inversion H; subst; auto.
  * simpl in *. destruct v; inversion H. subst. auto.
  * simpl. simpl in H. destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion H.
    subst. erewrite length_app, IHp1, IHp2. reflexivity. all: eauto.
Qed.
