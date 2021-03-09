Require Export ExpSyntax.
Export PeanoNat.
(* Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FSets.FMapFacts. *)

Import ListNotations.

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

  Proposition funid_eqb_eq (f f' : FunctionIdentifier):
    funid_eqb f f' = true <-> f = f'.
  Proof.
    intuition.
    * destruct f, f'. simpl in H. apply Bool.andb_true_iff in H. destruct H.
      apply eqb_eq in H. apply Nat.eqb_eq in H0. subst. reflexivity.
    * subst. destruct f'. simpl. rewrite eqb_refl, Nat.eqb_refl. auto.
  Qed.

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

  Proposition funid_eqb_refl (f : FunctionIdentifier) :
    funid_eqb f f = true.
  Proof.
    destruct f. simpl. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  Qed.

  Proposition var_funid_eqb_refl (var : Var + FunctionIdentifier) :
    var_funid_eqb var var = true.
  Proof.
    destruct var.
    * simpl. apply eqb_refl.
    * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  Qed.

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
 | ERecFun f vl e => if funid_eqb f f' 
                     then ERecFun f vl e
                     else ERecFun f vl (funsubst f' what e)
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

Inductive list_forall {A : Type} (P : A -> Prop) : list A -> Prop :=
| forall_nil : list_forall P []
| forall_cons x xs : P x -> list_forall P xs -> list_forall P (x::xs).



Fixpoint eval_list (f : Exp -> @ResultType Exp) (l : list Exp) : @ResultType (list Exp) :=
match l with
| [] => Res []
| x::xs => match f x with
           | Res v => match eval_list f xs with
                       | Res vs => Res (v::vs)
                       | r => r
                       end
           | Fail => Fail
           | Timeout => Timeout
           end
end.

Fixpoint eval (clock : nat) (e : Exp) : @ResultType Exp :=
match clock with
| 0 => Timeout
| S n => match e with
         | ELit l => Res (ELit l)
         | EVar v => Fail
         | EFunId f => Fail
         | EFun vl e => Res (EFun vl e)
         | ERecFun f vl e => Res (ERecFun f vl e)
         | EApp exp l => match eval n exp with
                         (** In Core Erlang this check only happens later *)
                         | Res (EFun vl e) =>
                            (* This would be better with Monads *)
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Res vals => 
                                 if length vals =? length vl
                                 then eval n (varsubst_list vl vals e)
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res (ERecFun f vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Res vals => 
                                 if length vals =? length vl
                                 then eval n (varsubst_list vl vals (funsubst f (ERecFun f vl e) e))
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res _ => Fail
                         | r => r
                         end
         | ELet v e1 e2 => match eval n e1 with
                           | Res val => eval n (varsubst v val e2)
                           | r      => r
                           end
         | ELetRec f vl b e => eval n (funsubst f (ERecFun f vl b) e)
         | EPlus e1 e2 => 
            match eval n e1, eval n e2 with
            | Res (ELit n), Res (ELit m) => Res (ELit (n + m))
            | Res _, Res _ => Fail
            | Res _, r => r
            | r, _     => r
            end
         | EIf e1 e2 e3 =>
            match eval n e1 with
            | Res (ELit 0) => eval n e2
            | Res _        => eval n e3
            | r            => r
            end
        end
end.

Theorem indexed_to_forall {A : Type} (l : list A) : forall P def,
  list_forall P l
<->
  (forall i, i < length l -> P (nth i l def)).
Proof.
  induction l; split; intros.
  * inversion H0.
  * constructor.
  * inversion H. subst. destruct i.
    - simpl. auto.
    - simpl. apply IHl. exact H4. simpl in H0. lia.
  * constructor.
    - apply (H 0). simpl. lia.
    - eapply IHl. intros. apply (H (S i)). simpl. lia.
Qed.

Theorem list_eval_eq_length (el : list Exp) : forall clock vl,
  eval_list (eval clock) el = Res vl -> length el = length vl.
Proof.
  induction el; intros; inversion H.
  * auto.
  * repeat break_match_hyp; try congruence. inversion H1. specialize (IHel _ _ Heqr0). simpl. lia.
Qed.

Theorem all_eval_single (el : list Exp) : forall clock v2,
  eval_list (eval clock) el = Res v2
->
  (forall i, i < length el -> eval clock (nth i el (ELit 0)) = Res (nth i v2 (ELit 0))).
Proof.
  induction el.
  * intros. inversion H0.
  * intros. simpl in H. repeat break_match_hyp; try congruence. inversion H. subst. destruct i.
    - exact Heqr.
    - simpl. apply IHel. exact Heqr0. simpl in H0. lia.
Qed.

Theorem list_result_is_value l : forall clock vals,
  (forall e v : Exp, eval clock e = Res v -> is_value v)
->
  eval_list (eval clock) l = Res vals
  ->
  forall i, i < length vals -> is_value (nth i vals (ELit 0)).
Proof.
  induction l; intros.
  * simpl in H0. inversion H0. subst. inversion H1.
  * simpl in H0. break_match_hyp; try congruence. apply H in Heqr.
    break_match_hyp; try congruence. inversion H0. subst.
    pose (IHl _ _ H Heqr0). destruct i.
    - simpl. auto.
    - apply i0. simpl in H1. lia.
Qed.

Theorem result_is_value :
  forall clock e v, eval clock e = Res v -> is_value v.
Proof.
  intro. induction clock; intros.
  * inversion H.
  * destruct e; inversion H.
    - constructor.
    - constructor.
    - constructor.
    - break_match_hyp; inversion H1. break_match_hyp; try congruence.
      + break_match_hyp; try congruence. break_match_hyp. 2: congruence. apply IHclock in H1. auto.
      + break_match_hyp; try congruence. break_match_hyp. 2: congruence. apply IHclock in H1. auto.
    - break_match_hyp; try congruence. apply IHclock in H1. auto.
    - apply IHclock in H1. auto.
    - break_match_hyp; try congruence. break_match_hyp; try congruence; break_match_hyp; try congruence.
      break_match_hyp; try congruence.
      + inversion H1. constructor.
    - break_match_hyp; try congruence. break_match_hyp; try congruence.
      destruct l; apply IHclock in H1; auto.
      all: apply IHclock in H1; auto.
Qed.

Lemma foo x :
  eval (10 + x) (sum 2) = Res (ELit 3).
Proof.
  simpl. auto.
Qed.

(** Congruence *)

(* Future work, based on https://github.com/cobbal/ppl-ctx-equiv-coq 
  Trick: avoid positivity check by using typing
*)

Axiom bigger_clock :
  forall e clock v clock', clock' >= clock ->
   eval clock  e = Res v ->
   eval clock' e = Res v.

Axiom bigger_clock_list :
  forall l clock v clock', clock' >= clock ->
    eval_list (eval clock) l = Res v ->
    eval_list (eval clock') l = Res v.

Definition terminating (e : Exp) : Prop :=
  exists v clock, eval clock e = Res v
.