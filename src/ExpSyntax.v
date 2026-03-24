(**

  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we describe the syntax of Core Erlang.

*)
Require Export SyntaxBasics.

Import ListNotations.

(** The syntax of expressions: *)
Inductive Exp : Set :=
| EExp (e : NonVal)
| VVal (v : Val)

with NonVal : Set :=
| EApp    (exp : Exp)     (l : list Exp)
| ELet    (e1 e2 : Exp)
(** Eliminator *)
| ECase (e : Exp) (p : Pat) (e1 e2 : Exp)
(** Lists *)
| ECons (e1 e2 : Exp)
| EReceive (l : list (Pat * Exp))
| EBIF (e : Exp) (l : list Exp)
(** We note, that both sequential and concurrent built-in functions
    are represented by EBIF, just like in Core Erlang itself.
*)

with Val : Set :=
| VLit    (l : Lit)
| VPid    (p : PID)
| VVar    (n : nat)
(** Instead of multiple fun constructs (recursive and non-recursive), 
    we use only recursive funs, which use the 0 DB-index as the recursive fun-exp *)
| VFun    (vl : nat) (e : Exp)
| VNil
(** Recursive data structures which are values: *)
| VCons (e1 e2 : Val)
(** Concurrency *)
.

Declare Scope sub_scope.
Delimit Scope sub_scope with sub.

Coercion EExp : NonVal >-> Exp.
Coercion VVal : Val >-> Exp.
Notation "˝ v" := (VVal v) (at level 11) : sub_scope.
Notation "° n" := (EExp n) (at level 11) : sub_scope.

Section correct_exp_ind.
(** Coq cannot automatically generate correct induction principle
    for expressions (because of mutual induction between Exp
    and list). Thus we define it by hand:
*)
  Variables
    (P : Exp -> Prop)
    (PV : Val -> Prop)
    (PN : NonVal -> Prop)
    (Q : list Exp -> Prop)
    (W : list (Pat * Exp) -> Prop).

  Hypotheses
   (HE1 : forall v : Val, PV v -> P (VVal v))
   (HE2 : forall v : NonVal, PN v -> P (EExp v))
   (H0 : forall (l : Lit), PV (VLit l))
   (H00 : forall (l : PID), PV (VPid l))
   (H1 : forall (n : nat), PV (VVar n))
   (H3 : forall (vl : nat) (e : Exp), P e -> PV (VFun vl e))
   (H5 : forall (e : Exp), P e -> forall (el : list Exp), Q el 
       -> PN (EApp e el))
   (H6 : forall (e1 : Exp), P e1 -> forall e2 : Exp, P e2 
       -> PN (ELet e1 e2))
   (H9 : forall (e1 : Exp), P e1 ->  forall e2, P e2 -> forall e3, P e3 -> forall p, PN (ECase e1 p e2 e3))
   (H10 : forall e1, P e1 -> forall e2, P e2 -> PN (ECons e1 e2))
   (H11 : PV VNil)
   (H12 : forall e1, PV e1 -> forall e2, PV e2 -> PV (VCons e1 e2))
   (H13 : forall e1, P e1 -> forall l, Q l -> PN (EBIF e1 l))
   (H14 : forall l, W l -> PN (EReceive l))
   (H1' : Q [])
   (H'  : forall e, P e -> forall l, Q l -> Q (e :: l))
   (J : W [])
   (J0 : forall e, P e -> forall xs, W xs -> forall p, W ((p, e)::xs)).

  Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | VVal v => HE1 v (Val_ind2 v)
  | EExp e => HE2 e (NonVal_ind2 e)
  end
  with NonVal_ind2 (e : NonVal) : PN e :=
  match e as x return PN x with
  | EApp e el => H5 e (Exp_ind2 e) el ((fix l_ind (l':list Exp) : Q l' :=
                                         match l' as x return Q x with
                                         | [] => H1'
                                         | v::xs => H' v (Exp_ind2 v) xs (l_ind xs)
                                         end) el)
  | ELet e1 e2 => H6 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ECase e p e1 e2 => H9 e (Exp_ind2 e) e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) p
  | ECons e1 e2 => H10 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | EBIF e l => H13 e (Exp_ind2 e) l ((fix l_ind (l':list Exp) : Q l' :=
                                         match l' as x return Q x with
                                         | [] => H1'
                                         | v::xs => H' v (Exp_ind2 v) xs (l_ind xs)
                                         end) l)
  | EReceive l => H14 l ((fix l_ind (l':list (Pat * Exp)) : W l' :=
                                         match l' as x return W x with
                                         | [] => J
                                         | (p, v)::xs => J0 v (Exp_ind2 v) xs (l_ind xs) p
                                         end) l)
  end
  with Val_ind2 (e : Val) : PV e :=
  match e as x return PV x with
  | VLit l => H0 l
  | VPid l => H00 l
  | VVar n => H1 n
  | VFun vl e => H3 vl e (Exp_ind2 e)
  | VNil => H11
  | VCons e1 e2 => H12 e1 (Val_ind2 e1) e2 (Val_ind2 e2)
  end.

End correct_exp_ind.

Fixpoint Exp_eq_dec (e e' : Exp) : {e = e'} + {e <> e'}
with NonVal_eq_dec (e e' : NonVal) : {e = e'} + {e <> e'}
with Val_eq_dec (e e' : Val) : {e = e'} + {e <> e'}.
Proof. all: repeat decide equality. Qed.

(** Examples *)
Open Scope sub_scope.
(** Incrementing expression *)
Definition inc (n : Z) := ELet (VLit n) (EBIF (VLit "+"%string) [˝VVar 0; ˝VLit 1%Z]).
(** Summation from 0 to the given positive number *)
Definition sum (n : Z) := ELet (VFun 1 (ECase (VVar 1) (PLit 0%Z) (VVar 1) (
                                            (EBIF (VLit "+"%string) [˝VVar 1;
                                            °EApp (VVar 0) [°EBIF (VLit "+"%string) [˝VVar 1; ˝VLit ((-1)%Z)]]]))))
                        (EApp (˝VVar 0) [˝VLit n]).
(** Application of a 0-parameter function inside `let`. *)
Definition simplefun (n : Z) := ELet (VFun 0 (VLit n)) (EApp (VVar 0) []).
(** Application of a two-parameter function, which sums these. *)
Definition simplefun2 (n m : Z) := EApp (VFun 2 (EBIF (VLit "+"%string) [˝VVar 1; ˝VVar 2])) [˝VLit n; ˝VLit m].

(** Map function expressed with `letrec`. It transforms the list with
    the given function value. *)
Definition obj_map f e : Exp :=
  ELet (VFun 2
    (ECase (VVar 2)
      (PCons PVar PVar) (ECons (EApp (VVar 3) [˝VVar 0])
                               (EApp (VVar 2) [˝VVar 3; ˝VVar 1]))
                        VNil
    ))
    (EApp (VVar 0) [f;e]).

(** Foldr function expressed with `letrec`. It aggregates a list. *)
Definition obj_foldr f e d : Exp :=
  ELet (VFun 3
    (ECase (VVar 3)
      (PCons PVar PVar) (EApp (VVar 3) [˝VVar 0; °EApp (VVar 2) [˝VVar 3; ˝VVar 4; ˝VVar 1]])
                        (VVar 2)
    ))
    (EApp (VVar 0) [f;d;e]).

(** Names, equalities *)

(* (* The equality of function signatures *)
Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
match v1, v2 with
| (fid1, num1), (fid2, num2) => String.eqb fid1 fid2 && Nat.eqb num1 num2
end.

Definition VarFunId : Type := Var + FunctionIdentifier.

(* Extended equality between functions and vars *)
Definition var_funid_eqb (v1 v2 : VarFunId) : bool :=
match v1, v2 with
| inl s1, inl s2 => String.eqb s1 s2
| inr f1, inr f2 => funid_eqb f1 f2
| _, _ => false
end.

Theorem funid_eq_dec : forall (a b : FunctionIdentifier), {a = b} + {a <> b}.
Proof. decide equality. apply Nat.eq_dec. apply string_dec. Qed.

Theorem var_funid_eq_dec : forall (a b : VarFunId), {a = b} + {a <> b}.
Proof. decide equality. apply string_dec. apply funid_eq_dec. Qed.

Proposition funid_eqb_eq (f f' : FunctionIdentifier):
  funid_eqb f f' = true <-> f = f'.
Proof.
  intuition.
  * destruct f, f'. simpl in H. apply Bool.andb_true_iff in H. destruct H.
    apply eqb_eq in H. apply Nat.eqb_eq in H0. subst. reflexivity.
  * subst. destruct f'. simpl. rewrite eqb_refl, Nat.eqb_refl. auto.
Qed.

Global Hint Resolve funid_eqb_eq : core.

Proposition funid_eqb_neq (f f0 : FunctionIdentifier):
  funid_eqb f f0 = false <-> f <> f0.
Proof.
  intuition.
  * destruct f, f0. simpl in H. apply Bool.andb_false_iff in H. inversion H.
      - apply eqb_neq in H1. unfold not in *. apply H1. inversion H0. reflexivity.
      - apply Nat.eqb_neq in H1. unfold not in *. apply H1. inversion H0. reflexivity.
  * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff.
      unfold not in H. case_eq ((s =? s0)%string); intros.
      - right. apply eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst. reflexivity.
      - left. reflexivity.
Qed.

Global Hint Resolve funid_eqb_neq : core.

Proposition var_funid_eqb_eq (v0 v : Var + FunctionIdentifier):
  var_funid_eqb v0 v = true <-> v0 = v.
Proof.
  intros. split; intros.
  { destruct v0, v.
    * inversion H. apply eqb_eq in H1. subst. reflexivity.
    * inversion H.
    * inversion H.
    * apply funid_eqb_eq in H. subst. auto.
  }
  { destruct v, v0.
    * inversion H. subst. simpl. apply eqb_refl.
    * inversion H.
    * inversion H.
    * simpl. apply funid_eqb_eq. inversion H. auto.
  }
Qed.

Global Hint Resolve var_funid_eqb_eq : core.

Proposition var_funid_eqb_neq (v0 v : Var + FunctionIdentifier):
  var_funid_eqb v0 v = false <-> v0 <> v.
Proof.
  split; intros.
  { destruct v0, v.
    * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. reflexivity.
    * unfold not. intro. inversion H0.
    * unfold not. intro. inversion H0.
    * apply funid_eqb_neq in H. intro. congruence.
  }
  { destruct v0, v.
    * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * apply funid_eqb_neq. intro. congruence.
  }
Qed.

Global Hint Resolve var_funid_eqb_neq : core.

Proposition funid_eqb_refl (f : FunctionIdentifier) :
  funid_eqb f f = true.
Proof.
  destruct f. simpl. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Global Hint Resolve funid_eqb_refl : core.

Proposition var_funid_eqb_refl (var : Var + FunctionIdentifier) :
  var_funid_eqb var var = true.
Proof.
  destruct var.
  * simpl. apply eqb_refl.
  * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Global Hint Resolve var_funid_eqb_refl : core. *)

Section in_list.
(** Bool-based In for Coq *)
Variable A : Type.
Variable (eqb : A -> A -> bool).
Hypothesis (eqb_true : forall e1 e2, eqb e1 e2 = true <-> e1 = e2).
Hypothesis (eqb_false: forall e1 e2, eqb e1 e2 = false <-> e1 <> e2).

Fixpoint in_list (v : A) (l : list A) : bool :=
match l with
| [] => false
| x::xs => if eqb v x then true else in_list v xs
end.

Theorem in_list_sound : forall l e, in_list e l = true <-> In e l.
Proof.
  induction l; intros.
  * split; intros; inversion H.
  * split; intros.
    - simpl in H. break_match_hyp.
      + apply eqb_true in Heqb. simpl. left. auto.
      + apply eqb_false in Heqb. simpl. right. apply IHl. auto.
    - destruct (eqb e a) eqn:P.
      + apply eqb_true in P. subst. simpl. break_match_goal; auto.
        rewrite eqb_false in Heqb. congruence.
      + simpl. rewrite P. apply IHl. inversion H.
        ** apply eqb_false in P. congruence.
        ** auto.
Qed.

Theorem not_in_list_sound : forall l e, in_list e l = false <-> ~In e l.
Proof.
  induction l; intros.
  * split; intros. intro. inversion H0. reflexivity.
  * split; intros.
    - simpl in H. break_match_hyp.
      + inversion H.
      + apply eqb_false in Heqb. simpl. intro. inversion H0. symmetry in H1. contradiction.
        eapply IHl; eauto.
    - simpl. break_match_goal. set_solver. set_solver.
Qed.

End in_list.

(** Pattern matching. Variable bindings in the nameless representation
    will be created in an ascending order. E.g. the matching for

    match_pattern (PCons (PVar PVar)) (VCons e₁ e₂)

    will be 0 ↦ e₁, 1 ↦ e₂
*)
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
