
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
| EVar    (n : nat) (v : Var)
| EFunId  (n : nat) (f : FunctionIdentifier)
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
   (H1 : forall (n : nat) (v : Var), P (EVar n v))
   (H2 : forall (n : nat) (f : FunctionIdentifier), P (EFunId n f))
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
  | EVar n s => H1 n s
  | EFunId n f => H2 n f
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

Fixpoint Exp_eq_dec (e e' : Exp) : {e = e'} + {e <> e'}.
Proof. repeat decide equality. Qed.

Definition XVar : Var := "X"%string.
Definition YVar : Var := "Y"%string.
Definition ZVar : Var := "Z"%string.

Definition F0 : FunctionIdentifier := ("f"%string, 0).
Definition F1 : FunctionIdentifier := ("f"%string, 1).

Definition inc (n : Z) := ELet XVar (ELit n) (EPlus (EVar 0 XVar) (ELit 1)).
Definition sum (n : Z) := ELetRec F1 [XVar] (EIf (EVar 1 XVar) (EVar 1 XVar) (
                                            (EPlus (EVar 1 XVar)
                                            (EApp (EFunId 0 F1) [EPlus (EVar 1 XVar) (ELit (-1))]))))
                        (EApp (EFunId 0 F1) [ELit n]).
Definition simplefun (n : Z) := ELet XVar (EFun [] (ELit n)) (EApp (EVar 0 XVar) []).
Definition simplefun2 (n m : Z) := EApp (EFun [XVar; YVar] (EPlus (EVar 0 XVar) (EVar 1 YVar))) [ELit n; ELit m].

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

Corollary app_not_in {T : Type} : forall (x:T) (l1 l2 : list T),
  ~In x l1 -> ~In x l2 -> ~In x (l1 ++ l2).
Proof.
  intros.
  intro. eapply in_app_or in H1. destruct H1; contradiction.
Qed.

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

Hint Resolve funid_eqb_eq.

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

Hint Resolve funid_eqb_neq.

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

Hint Resolve var_funid_eqb_eq.

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

Hint Resolve var_funid_eqb_neq.

Proposition funid_eqb_refl (f : FunctionIdentifier) :
  funid_eqb f f = true.
Proof.
  destruct f. simpl. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Hint Resolve funid_eqb_refl.

Proposition var_funid_eqb_refl (var : Var + FunctionIdentifier) :
  var_funid_eqb var var = true.
Proof.
  destruct var.
  * simpl. apply eqb_refl.
  * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Hint Resolve var_funid_eqb_refl.

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

Hint Resolve in_list_sound.
Hint Resolve not_in_list_sound.

Definition Renaming : Type := nat -> nat.

Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iterate f n' a)
  end.

Notation uprenn := (iterate upren).

Fixpoint rename (ρ : Renaming) (e : Exp) : Exp :=
match e with
 | ELit l => e
 | EVar n v => EVar (ρ n) v
 | EFunId n f => EFunId (ρ n) f
 | EFun vl e => EFun vl (rename (uprenn (length vl) ρ) e)
 | ERecFun f vl e => ERecFun f vl (rename (uprenn (1 + length vl) ρ) e)
 | EApp exp l => EApp (rename ρ exp) (map (rename ρ) l)
 | ELet v e1 e2 => ELet v (rename ρ e1) (rename (upren ρ) e2)
 | ELetRec f vl b e => ELetRec f vl (rename (uprenn (1 + length vl) ρ) b) 
                                    (rename (upren ρ) e)
 | EPlus e1 e2 => EPlus (rename ρ e1) (rename ρ e2)
 | EIf e1 e2 e3 => EIf (rename ρ e1) (rename ρ e2) (rename ρ e3)
end.

Definition Substitution := nat -> Exp + nat. (* We need to have the names for the identity elements explicitly, because of the shiftings (up, upn) *)
Definition idsubst : Substitution := fun x => inr x.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => match (ξ x') with
              | inl exp => inl (rename (fun n => S n) exp)
              | inr num => inr (S num)
              end
    end.

Notation upn := (iterate up_subst).

(* Definition restrict_subst (ξ : Substitution) (n : nat) : Substitution :=
  fun (x : VarFunId) =>
    if in_list x vl
    then idsubst x
    else ξ x
.

Notation "ξ -- vl" := (restrict_subst ξ vl) (at level 70). *)

Fixpoint subst (ξ : Substitution) (base : Exp) : Exp :=
match base with
 | ELit l => base
 | EVar n v => match ξ n with
               | inl exp => exp
               | inr num => EVar num v
               end
 | EFunId n f => match ξ n with
                 | inl exp => exp
                 | inr num => EFunId num f
                 end
 | EFun vl e => EFun vl (subst (upn (length vl) ξ) e)
 | ERecFun f vl e => ERecFun f vl (subst (upn (1 + length vl) ξ) e)
 | EApp exp l => EApp (subst ξ exp) (map (subst ξ) l)
 | ELet v e1 e2 => ELet v (subst ξ e1) (subst (up_subst ξ) e2)
 | ELetRec f vl b e => ELetRec f vl (subst (upn (1 + length vl) ξ) b)
                                    (subst (up_subst ξ) e)
 | EPlus e1 e2 => EPlus (subst ξ e1) (subst ξ e2)
 | EIf e1 e2 e3 => EIf (subst ξ e1) (subst ξ e2) (subst ξ e3)
end.

(* Definition extend_subst (ξ : Substitution) (x : VarFunId) (e : Exp) : Substitution :=
  fun y =>
    if var_funid_eqb x y
    then e
    else ξ y.

Notation "ξ [[ x ::= e ]]" := (extend_subst ξ x e) (at level 80).

Definition extend_subst_list (ξ : Substitution) (l : list (VarFunId * Exp)) : Substitution :=
  fold_left (fun ξ' '(x, e) => extend_subst ξ' x e) l ξ.

Notation "ξ [[ ::= l ]]" := (extend_subst_list ξ l) (at level 80). *)

Definition scons {X : Type} (s : X) (σ : nat -> X) (x : nat) : X :=
  match x with 
  | S y => σ y
  | _ => s
  end.
Notation "s .: σ" := (scons (inl s) σ) (at level 55, σ at level 56, right associativity).
Notation "s .[ σ ]" := (subst σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).
Notation "s .[ t /]" := (subst (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]").
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons (t1) (scons (t2) .. (scons (tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").

(* Tests: *)
Goal (inc 1).[ELit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (inc 1).[ELit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (EVar 0 XVar) [EVar 0 XVar; ELet XVar (EVar 0 XVar) (EVar 0 XVar)]).[ELit 0/]
  = (EApp (ELit 0) [ELit 0; ELet XVar (ELit 0) (EVar 0 XVar)]). Proof. reflexivity. Qed.

Compute (ELit 0 .: ELit 0 .: idsubst) 3.

Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.