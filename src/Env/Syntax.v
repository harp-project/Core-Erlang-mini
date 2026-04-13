From CoreErlang Require Export SyntaxBasics.
From stdpp Require Export base list.

(** The syntax of expressions: *)
Inductive Exp : Set :=
| EExp (e : NonVal)
| VVal (v : Val)

with NonVal : Set :=
(** Instead of multiple fun constructs (recursive and non-recursive), 
    we use only recursive funs, which use the 0 DB-index as the recursive fun-exp *)
| EFun    (vl : nat) (e : Exp)
| EApp    (exp : Exp)     (l : list Exp)
| ELet    (e1 e2 : Exp)
(** Eliminator *)
| ECase (e : Exp) (p : Pat) (e1 e2 : Exp)
(** Lists *)
| ECons (e1 e2 : Exp)
(** Concurrency *)
(* | EReceive (l : list (Pat * Exp)) *)
| EBIF (e : Exp) (l : list Exp)
| EVar    (n : nat) (* !!! *)

with Val : Set :=
| VLit    (l : Lit)
| VPid    (p : PID)
(** Variables and function identifiers are just indices.
    TODO: In the future, function identifiers should include the arity too!
*)
| VNil
(** Recursive data structures which are values: *)
| VCons (e1 e2 : Val)
| VClos (Γ : list Val) (vl : nat) (e : Exp).

Declare Scope env_scope.
Delimit Scope env_scope with env.

Coercion EExp : NonVal >-> Exp.
Coercion VVal : Val >-> Exp.
Notation "˝ v" := (VVal v) (at level 11) : env_scope.
Notation "° n" := (EExp n) (at level 11) : env_scope.


Section correct_ind.

Variables (P : Exp -> Prop) (PN : NonVal -> Prop) (PV : Val -> Prop)
          (Q : list Exp -> Prop) (R : list Val -> Prop).

Hypotheses
  (HEExp : forall (nv : NonVal), PN nv -> P (EExp nv))
  (HVVal : forall (v : Val), PV v -> P (VVal v))

  (HNF_Fun : forall (vl : nat) (e : Exp), P e -> PN (EFun vl e))
  (HNF_App : forall (e : Exp), P e -> forall (el : list Exp), Q el -> PN (EApp e el))
  (HNF_Let : forall (e1 e2 : Exp), P e1 -> P e2 -> PN (ELet e1 e2))
  (HNF_Case : forall (e : Exp) (p : Pat) (e1 e2 : Exp), P e -> P e1 -> P e2 -> PN (ECase e p e1 e2))
  (HNF_Cons : forall (e1 e2 : Exp), P e1 -> P e2 -> PN (ECons e1 e2))
  (HNF_EBIF : forall (e : Exp), P e -> forall (l : list Exp), Q l -> PN (EBIF e l))
  (HNF_Var : forall (n : nat), PN (EVar n))

  (HV_Lit : forall (l : Lit), PV (VLit l))
  (HV_Pid : forall (n : nat), PV (VPid n))
  (HV_Nil : PV VNil)
  (HV_Cons : forall (v1 v2 : Val), PV v1 -> PV v2 -> PV (VCons v1 v2))
  (HV_Clos : forall (Gamma : list Val) (vl : nat) (e : Exp), R Gamma -> P e -> PV (VClos Gamma vl e))

  (HQ_nil : Q [])
  (HQ_cons : forall (e : Exp), P e -> forall (l : list Exp), Q l -> Q (e :: l))

  (HR_nil : R [])
  (HR_cons : forall (v : Val), PV v -> forall (l : list Val), R l -> R (v :: l)).

Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | EExp nv => HEExp nv (NonVal_ind2 nv)
  | VVal v => HVVal v (Val_ind2 v)
  end

with NonVal_ind2 (nv : NonVal) : PN nv :=
  match nv as x return PN x with
  | EFun vl e => HNF_Fun vl e (Exp_ind2 e)
  | EApp e el => HNF_App e (Exp_ind2 e) el (
      (fix l_ind (l' : list Exp) : Q l' :=
         match l' as y return Q y with
         | [] => HQ_nil
         | v::xs => HQ_cons v (Exp_ind2 v) xs (l_ind xs)
         end) el)
  | ELet e1 e2 => HNF_Let e1 e2 (Exp_ind2 e1) (Exp_ind2 e2)
  | ECase e p e1 e2 => HNF_Case e p e1 e2 (Exp_ind2 e) (Exp_ind2 e1) (Exp_ind2 e2)
  | ECons e1 e2 => HNF_Cons e1 e2 (Exp_ind2 e1) (Exp_ind2 e2)
  | EBIF e l => HNF_EBIF e (Exp_ind2 e) l (
      (fix l_ind (l' : list Exp) : Q l' :=
         match l' as y return Q y with
         | [] => HQ_nil
         | v::xs => HQ_cons v (Exp_ind2 v) xs (l_ind xs)
         end) l)
  | EVar n => HNF_Var n
  end

with Val_ind2 (v : Val) : PV v :=
  match v as x return PV x with
  | VLit l => HV_Lit l
  | VPid p => HV_Pid p
  | VNil => HV_Nil
  | VCons v1 v2 => HV_Cons v1 v2 (Val_ind2 v1) (Val_ind2 v2)
  | VClos Gamma vl e => HV_Clos Gamma vl e (
      (fix lV_ind (l' : list Val) : R l' :=
         match l' as y return R y with
         | [] => HR_nil
         | v::xs => HR_cons v (Val_ind2 v) xs (lV_ind xs)
         end) Gamma) (Exp_ind2 e)
  end.

  Combined Scheme Env_Exp_full_ind from Exp_ind2, NonVal_ind2, Val_ind2.

End correct_ind.

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

