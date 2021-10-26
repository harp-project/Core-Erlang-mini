
From Coq Require Export ZArith.BinInt
                        FunctionalExtensionality
                        Strings.String.
Require Export Basics.

Import ListNotations.

Definition Var : Set := string.

Definition FunctionIdentifier : Set := string * nat.

Inductive Pat : Set :=
| PLit (l : Z)
| PVar (** will be assigned in increasing order *)
| PNil
| PCons (p1 p2 : Pat).

Inductive Exp : Set :=
| ELit    (l : Z)
| EVar    (n : nat) (** (v : Var) <- these will be assigned by a naming function *)
| EFunId  (n : nat) (** (f : FunctionIdentifier) <- these will be assigned by a naming function *)
(** Instead of multiple fun-s (recursive and non-recursive), 
    we use only recursive funs, which use the 0 DB-index as the recursive fun-exp *)
| EFun    (vl : list Var) (e : Exp)
| EApp    (exp : Exp)     (l : list Exp)
| ELet    (v : Var) (e1 e2 : Exp)
| ELetRec (f : FunctionIdentifier) (vl : list Var) (b e : Exp)
(** Techical helper constructions: 1) simple bif: plus, 2) simple case: if *)
| EPlus   (e1 e2 : Exp)
(** Eliminator *)
| ECase (e : Exp) (p : Pat) (e1 e2 : Exp)
(** Lists *)
| ECons (e1 e2 : Exp)
| ENil
(** Recursive data structures which are values: *)
| VCons (e1 e2 : Exp).

Section correct_exp_ind.

  Variables
    (P : Exp -> Prop)(Q : list Exp -> Prop).

  Hypotheses
   (H0 : forall (l : Z), P (ELit l))
   (H1 : forall (n : nat), P (EVar n))
   (H2 : forall (n : nat), P (EFunId n))
   (H3 : forall (vl : list Var) (e : Exp), P e -> P (EFun vl e))
   (H5 : forall (e : Exp), P e -> forall (el : list Exp), Q el 
       -> P (EApp e el))
   (H6 : forall (v : Var) (e1 : Exp), P e1 -> forall e2 : Exp, P e2 
       -> P (ELet v e1 e2))
   (H7 : forall (f : FunctionIdentifier) (vl : list Var) (b : Exp), P b -> forall e : Exp, P e 
       -> P (ELetRec f vl b e))
   (H8 : forall (e1 : Exp), P e1 -> forall e2 : Exp, P e2 
       -> P (EPlus e1 e2))
   (H9 : forall (e1 : Exp), P e1 ->  forall e2, P e2 -> forall e3, P e3 -> forall p, P (ECase e1 p e2 e3))
   (H10 : forall e1, P e1 -> forall e2, P e2 -> P (ECons e1 e2))
   (H11 : P ENil)
   (H12 : forall e1, P e1 -> forall e2, P e2 -> P (VCons e1 e2))
   (H' : forall v : Exp, P v -> forall l:list Exp, Q l -> Q (v :: l))
   (H1' : Q []).

  Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | ELit l => H0 l
  | EVar n => H1 n
  | EFunId n => H2 n
  | EFun vl e => H3 vl e (Exp_ind2 e)
  | EApp e el => H5 e (Exp_ind2 e) el ((fix l_ind (l':list Exp) : Q l' :=
                                         match l' as x return Q x with
                                         | [] => H1'
                                         | v::xs => H' v (Exp_ind2 v) xs (l_ind xs)
                                         end) el)
  | ELet v e1 e2 => H6 v e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ELetRec f vl b e => H7 f vl b (Exp_ind2 b) e (Exp_ind2 e)
  | EPlus e1 e2 => H8 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ECase e p e1 e2 => H9 e (Exp_ind2 e) e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) p
  | ECons e1 e2 => H10 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ENil => H11
  | VCons e1 e2 => H12 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  end.

End correct_exp_ind.

Fixpoint Exp_eq_dec (e e' : Exp) : {e = e'} + {e <> e'}.
Proof. repeat decide equality. Qed.

(** Examples *)

Definition XVar : Var := "X"%string.
Definition YVar : Var := "Y"%string.
Definition ZVar : Var := "Z"%string.

Definition F0 : FunctionIdentifier := ("f"%string, 0).
Definition F1 : FunctionIdentifier := ("f"%string, 1).

Definition inc (n : Z) := ELet XVar (ELit n) (EPlus (EVar 0) (ELit 1)).
Definition sum (n : Z) := ELetRec F1 [XVar] (ECase (EVar 1) (PLit 0) (EVar 1) (
                                            (EPlus (EVar 1)
                                            (EApp (EFunId 0) [EPlus (EVar 1) (ELit (-1))]))))
                        (EApp (EFunId 0) [ELit n]).
Definition simplefun (n : Z) := ELet XVar (EFun [] (ELit n)) (EApp (EVar 0) []).
Definition simplefun2 (n m : Z) := EApp (EFun [XVar; YVar] (EPlus (EVar 1) (EVar 2))) [ELit n; ELit m].


(** Names, equalities *)

(* The equality of function signatures *)
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

Global Hint Resolve var_funid_eqb_refl : core.

Fixpoint in_list (v : VarFunId) (l : list VarFunId) : bool :=
match l with
| [] => false
| x::xs => if var_funid_eqb v x then true else in_list v xs
end.

Theorem in_list_sound : forall l e, in_list e l = true <-> In e l.
Proof.
  induction l; intros.
  * split; intros; inversion H.
  * split; intros.
    - simpl in H. break_match_hyp.
      + apply var_funid_eqb_eq in Heqb. simpl. left. auto.
      + apply var_funid_eqb_neq in Heqb. simpl. right. apply IHl. auto.
    - destruct (var_funid_eqb e a) eqn:P.
      + apply var_funid_eqb_eq in P. subst. simpl. rewrite var_funid_eqb_refl. auto.
      + simpl. rewrite P. apply IHl. inversion H.
        ** apply var_funid_eqb_neq in P. congruence.
        ** auto.
Qed.

Theorem not_in_list_sound : forall l e, in_list e l = false <-> ~In e l.
Proof.
  induction l; intros.
  * split; intros. intro. inversion H0. reflexivity.
  * split; intros.
    - simpl in H. break_match_hyp.
      + inversion H.
      + apply var_funid_eqb_neq in Heqb. simpl. intro. inversion H0. symmetry in H1. contradiction.
        eapply IHl; eauto.
    - simpl. break_match_goal.
      apply var_funid_eqb_eq in Heqb. subst. exfalso. apply H. intuition.
      apply var_funid_eqb_neq in Heqb. eapply IHl. apply not_in_cons in H. destruct H. auto.
Qed.

Global Hint Resolve in_list_sound : core.
Global Hint Resolve not_in_list_sound : core.

Fixpoint match_pattern (p : Pat) (e : Exp) : option (list Exp) :=
match p with
| PVar => Some [e]
| PNil => match e with
          | ENil => Some []
          | _    => None
          end
| PLit l0 => match e with
             | ELit l => if Z.eqb l l0 then Some [] else None
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
 | PLit l => 0
 | PVar => 1
 | PNil => 0
 | PCons p1 p2 => pat_vars p1 + pat_vars p2
end.

Lemma match_pattern_length : forall p v l,
  match_pattern p v = Some l -> pat_vars p = length l.
Proof.
  induction p; intros.
  * simpl in *. destruct v; inversion H. break_match_hyp; now inversion H.
  * simpl in *. destruct v; inversion H; subst; auto.
  * simpl in *. destruct v; inversion H. subst. auto.
  * simpl. simpl in H. destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion H.
    subst. erewrite app_length, IHp1, IHp2. reflexivity. all: eauto.
Qed.
