Require Export ExpSyntax.
Export PeanoNat.
(* Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FSets.FMapFacts. *)

Import ListNotations.

Inductive is_value : Exp -> Prop :=
| ELit_val : forall l, is_value (ELit l)
| EFun_val : forall vl e, is_value (EFun vl e)
| ERecFun_val : forall f vl e, is_value (ERecFun f vl e).

Inductive ResultType {T : Set} : Set :=
| Timeout
| Fail
| Res (v : T)
.

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
                                 then eval n (subst (idsubst[[::= combine (map inl vl) vals]]) e)
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res (ERecFun f vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Res vals => 
                                 if length vals =? length vl
                                 then eval n (subst (idsubst[[::= (inr f, ERecFun f vl e) :: combine (map inl vl) vals]]) e)
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res _ => Fail
                         | r => r
                         end
         | ELet v e1 e2 => match eval n e1 with
                           | Res val => eval n (subst (idsubst[[inl v ::= val]]) e2)
                           | r      => r
                           end
         | ELetRec f vl b e => eval n (subst (idsubst[[inr f ::= ERecFun f vl b]]) e)
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

Goal eval 10 (inc 2) = Res (ELit 3). Proof. auto. Qed.
Goal eval 10 (simplefun 10) = Res (ELit 10). Proof. simpl. auto. Qed.
Goal eval 10 (sum 2) = Res (ELit 3). Proof. simpl. auto. Qed.
Goal eval 100 (sum 10) = Res (ELit 55). Proof. simpl. auto. Qed.
Goal eval 100 (simplefun2 10 10) = Res (ELit 20). Proof. simpl. auto. Qed.

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