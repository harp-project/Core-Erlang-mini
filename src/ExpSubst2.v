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

Definition E_rel (V_rel : relation Exp) (e1 e2 : Exp) : Prop :=
  ((terminating e1) <-> (terminating e2)) /\
  (forall clock v1 v2,
    eval clock e1 = Res v1 /\
    eval clock e2 = Res v2 ->
    V_rel v1 v2)
.

Lemma E_rel_refl : forall (V_rel : relation Exp),
  (forall x, is_value x -> V_rel x x)
->
  Reflexive (E_rel V_rel).
Proof.
  intros. unfold Reflexive, E_rel in *. intros. split.
  * split; intros; auto.
  * intros. destruct H0. rewrite H0 in H1. inversion H1. subst. apply H.
    eapply result_is_value. exact H0.
Qed.

Lemma E_rel_sym : forall (V_rel : relation Exp),
  Symmetric V_rel
->
  (forall e e', E_rel V_rel e e' -> E_rel V_rel e' e).
Proof.
  intros. unfold Symmetric, E_rel in *. destruct H0. intros. split.
  * symmetry. auto.
  * intros. destruct H2. apply H. eapply H1. split. exact H3. auto.
Qed.

Lemma E_rel_trans : forall (V_rel : relation Exp),
  Transitive V_rel
->
  (forall e e' e'', E_rel V_rel e e' -> E_rel V_rel e' e''
  ->
  E_rel V_rel e e'').
Proof.
  intros. unfold Transitive, E_rel in *. destruct H0, H1. intros. split.
  * eapply iff_trans. exact H0. auto.
  * intros. destruct H4, H0, H1. assert (exists v3 clock, eval clock e' = Res v3).
    { apply H0. eexists. eexists. exact H4. }
    destruct H8, H8.
    apply bigger_clock with (clock' := clock + x0) in H4.
    apply bigger_clock with (clock' := clock + x0) in H8.
    apply bigger_clock with (clock' := clock + x0) in H5. 2-4: lia.
    pose (H2 _ _ _ (conj H4 H8)). pose (H3 _ _ _ (conj H8 H5)). eapply H. exact v. auto.
Qed.

Inductive V_rel_base (valr : relation Exp) : relation Exp :=
| refl_base v : is_value v -> V_rel_base valr v v
| clos_rel2 vl b vl' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
      (forall i, i < length vl -> is_value (nth i vals1 (ELit 0))) ->
      (forall i, i < length vl -> is_value (nth i vals2 (ELit 0))) ->
    (forall i, i < length vl -> 
    valr (nth i vals1 (ELit 0)) (nth i vals2 (ELit 0))) ->
  E_rel valr (varsubst_list vl vals1 b) (varsubst_list vl' vals2 b'))
->
  V_rel_base valr (EFun vl b) (EFun vl' b')

| rec_clos_rel2 f vl b f' vl' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> is_value (nth i vals1 (ELit 0))) ->
    (forall i, i < length vl -> is_value (nth i vals2 (ELit 0))) ->
    (forall i, i < length vl -> 
     valr (nth i vals1 (ELit 0)) (nth i vals2 (ELit 0))) ->
  E_rel valr (varsubst_list vl vals1 (funsubst f (ERecFun f vl b) b))
             (varsubst_list vl' vals2 (funsubst f' (ERecFun f' vl' b') b')))
->
  V_rel_base valr (ERecFun f vl b) (ERecFun f' vl' b')
.

Lemma V_rel_base_refl : forall vrel x, is_value x -> (V_rel_base vrel) x x.
Proof.
  intros. constructor. auto.
Qed.

Lemma V_rel_base_sym : forall vrel, Symmetric vrel -> Symmetric (V_rel_base vrel).
Proof.
  intros. intro. intros. inversion H0; subst.
  * apply V_rel_base_refl. auto.
  * constructor. auto. intros. apply E_rel_sym. auto. apply H2; auto. intros. apply H6. lia.
    intros. apply H5. lia. intros. apply H. apply H7. lia.
  * constructor. auto. intros. apply E_rel_sym. auto. apply H2; auto. intros. apply H6. lia.
    intros. apply H5. lia. intros. apply H. apply H7. lia.
Qed.

Lemma V_rel_base_trans : forall (vrel : Exp -> Exp -> Prop),
  (forall x, is_value x -> vrel x x) ->
  Transitive vrel
->
  Transitive (V_rel_base vrel).
Proof.
  intros. intro. intros. inversion H1; inversion H2; subst; auto.
  * inversion H9. subst. constructor. lia. intros. eapply E_rel_trans. auto.
    apply H4; auto. lia. apply H8; auto. lia. intros. apply H10. lia. intros. apply H11. lia.
    intros. apply H12. lia.
  * inversion H9.
  * inversion H9.
  * inversion H9. subst. constructor. lia. intros. eapply E_rel_trans. auto.
    apply H4; auto. lia. apply H8; auto. lia. intros. apply H10. lia. intros. apply H11. lia.
    intros. apply H12. lia.
Qed.


Fixpoint V_rel (n : nat) : relation Exp :=
fun v1 v2 =>
match n with
| 0 => (* False *) v1 = v2
| S n' => V_rel_base (V_rel n') v1 v2
end.

Theorem V_rel_refl :
  forall n x, is_value x -> (V_rel n) x x.
Proof.
  induction n.
  * simpl. auto.
  * simpl. constructor. auto.
Qed.

Theorem V_rel_sym :
  forall n x1 x2, (V_rel n) x1 x2 -> (V_rel n) x2 x1.
Proof.
  induction n; intros.
  * simpl in *. auto.
  * simpl in *. apply V_rel_base_sym. unfold Symmetric; intros. apply IHn. auto. auto.
Qed.

Theorem V_rel_trans :
  forall n, Transitive (V_rel n).
Proof.
  induction n; unfold Transitive; intros; simpl in *.
  * subst. auto.
  * eapply V_rel_base_trans. 3: apply H. 3: apply H0.
    2: apply IHn.
    apply V_rel_refl. 
Qed.

Fixpoint size (e : Exp) : nat :=
match e with
 | ELit l => 1
 | EVar v => 1
 | EFunId f => 1
 | EFun vl e => 1 + size e
 | ERecFun f vl e => 1 + size e
 | EApp exp l => 1 + size exp + fold_right (fun x acc => size x + acc) 0 l
 | ELet v e1 e2 => 1 + size e1 + size e2
 | ELetRec f vl b e => 1 + size b + size e
 | EPlus e1 e2 => 1 + size e1 + size e2
 | EIf e1 e2 e3 => 1 + size e1 + size e2 + size e3
end.

(* For closed expressions: *)
Definition Equiv_rel_size e1 e2 : Prop := E_rel (V_rel (size e1 + size e2)) e1 e2.

Theorem size_inc_exp :
  forall n,
  (forall v1 v2 : Exp, is_value v1 -> is_value v2 -> V_rel n v1 v2 -> V_rel (S n) v1 v2) ->
  forall e1 e2, E_rel (V_rel n) e1 e2 -> E_rel (V_rel (S n)) e1 e2.
Proof.
  intros. destruct H0.
  constructor. auto. intros.
  specialize (H1 _ _ _ H2). destruct H2. apply result_is_value in H2. apply result_is_value in H3.
  apply H; auto.
Qed.


Theorem size_inc : forall n v1 v2, 
  is_value v1 -> is_value v2 ->
  V_rel n v1 v2 -> V_rel (S n) v1 v2.
Proof.
  induction n; intros.
  * simpl in H1. subst. eapply V_rel_refl. auto.
  * simpl in H1. simpl. inversion H1.
    - subst. eapply V_rel_base_refl. auto.
    - subst. remember (S n) as n'. simpl. constructor. auto. intros.
      specialize (H3 vals1 vals2 H4 H5 H6 H7).
      rewrite Heqn'. apply size_inc_exp. rewrite Heqn' in IHn. apply IHn. apply H3.
      intros. specialize (H8 i H9).
      assert ().
     { intros. unfold E_rel.
Abort.

Theorem Equiv_rel_size_refl : Reflexive Equiv_rel_size.
Proof. unfold Reflexive. intros. apply E_rel_refl. apply V_rel_refl. Qed.

Theorem Equiv_rel_size_sym : Symmetric Equiv_rel_size.
Proof.
  unfold Symmetric. intros. apply E_rel_sym.
  * unfold Symmetric. apply V_rel_sym.
  * rewrite Nat.add_comm. exact H.
Qed.

Theorem Equiv_rel_size_trans : Transitive Equiv_rel_size.
Proof.
  unfold Transitive. intros.
  eapply E_rel_trans.
  * apply V_rel_trans.
  * admit.
  * admit.
Abort.

(* Definition Equiv_rel_ex e1 e2 : Prop := exists n, E_rel (V_rel n) e1 e2.

Theorem Equiv_rel_ex_refl : Reflexive Equiv_rel_ex.
Proof. unfold Reflexive. intros. eexists. apply E_rel_refl. apply V_rel_refl. Unshelve. exact 0. Qed.

Theorem Equiv_rel_ex_sym : Symmetric Equiv_rel_ex.
Proof.
  unfold Symmetric. intros. destruct H. exists x0. apply E_rel_sym.
  * unfold Symmetric. apply V_rel_sym.
  * exact H.
Qed.

Theorem Equiv_rel_size_trans : Transitive Equiv_rel_ex.
Proof.
  unfold Transitive. intros. destruct H. destruct H0. *)

(* Program Fixpoint V_rel v1 v2 : Prop :=
match size v1, size v2 with
| 1, 1 => match v1, v2 with
          | ELit n, ELit m => n = m
          | _, _ => False
          end
| S n', S m' =>
  match v1, v2 with
  | EFun _ _, EFun _ _ => V_rel_fun (V_rel n') v1 v2
  | ERecFun _ _ _, ERecFun _ _ _ => V_rel_fun (V_rel n') v1 v2
  | _, _ => False
  end
end. *)

Lemma V_rel_sym n :
  Symmetric (V_rel n).
Proof.
  unfold Symmetric. induction n; intros.
  * simpl in *. auto.
  * destruct x, y; inversion H; simpl.
    - apply V_rel_num_refl.
    - apply V_rel_fun_sym. subst. unfold Symmetric. intros. apply IHn. auto.
      subst. simpl in H. auto.
    - apply V_rel_fun_sym. subst. unfold Symmetric. intros. apply IHn. auto.
      subst. simpl in H. auto.
Qed.

(* For closed expressions: *)
Definition Equiv_rel_size e1 e2 : Prop := E_rel (V_rel (size e1 + size e2)) e1 e2.

Lemma V_rel_trans n :
  Transitive (V_rel n).
Proof.
  unfold Transitive. induction n; intros.
  * simpl in *. subst. auto.
  * destruct x, y, z; inversion H; inversion H0; simpl.
    - apply V_rel_num_refl.
    - eapply V_rel_fun_trans. (* reflexivity needed :( *)
Abort.

Theorem V_Rel_increase n :
  forall v1 v2, V_rel n v1 v2 -> V_rel (S n) v1 v2.
Proof.
  induction n; intros.
  * simpl in H. subst. simpl. (* reflexivity needed :( *)
Abort.

(* Lemma v_rel_refl n :
  forall x, is_value x -> V_rel n x x.
Proof.
  induction n.
  * unfold Reflexive. intros. simpl. auto.
  * unfold Reflexive in *. intros. destruct x; try inversion H.
    - simpl. apply V_rel_num_refl.
    - simpl. constructor. auto. intros. split.
      + admit. (* Equivalent environments *)
      + intros. destruct H5. subst.
Abort. *)

(* For closed expressions: *)
Definition Equiv_rel n := E_rel (V_rel n).

Theorem is_value_eval :
  forall v, is_value v -> 
  forall clock, eval (S clock) v = Res v.
Proof.
  intros. destruct H; reflexivity.
Qed.

Theorem is_value_term v :
  is_value v -> terminating v.
Proof.
  intros. destruct H; eexists; exists 1; reflexivity.
Qed.

Theorem subst_comm :
  forall e v1 val1 v2 val2, v1 <> v2 ->
  (varsubst v1 val1 (varsubst v2 val2 e)) = (varsubst v2 val2 (varsubst v1 val1 e)).
Proof.

Admitted.

Theorem subst_shadow :
  forall e v val1 val2,
  (varsubst v val1 (varsubst v val2 e)) = (varsubst v val1 e).
Proof.

Admitted.

Lemma alma1_list l : forall clock v v1 v2 res1,
  (forall (e : Exp) (v : Var) (v1 v2 res1 : Exp),
          is_value v1 ->
          is_value v2 ->
          eval clock (varsubst v v1 e) = Res res1 ->
          exists (res2 : Exp) (clock : nat), eval clock (varsubst v v2 e) = Res res2) ->
  is_value v1 -> is_value v2 ->
  eval_list (eval clock) (map (varsubst v v1) l) = Res res1
->
  exists res2 clock, eval_list (eval clock) (map (varsubst v v2) l) = Res res2.
Proof.
  induction l; intros.
  * simpl. exists [], 1. reflexivity.
  * simpl in H2. repeat break_match_hyp; try congruence. inversion H2. subst.
    apply H with (v2 := v2) in Heqr. apply IHl with (v2 := v2) in Heqr0. destruct Heqr, Heqr0, H3, H4.
    exists (x :: x0), (x1 + x2). simpl. eapply bigger_clock in H3. rewrite H3.
    eapply bigger_clock_list in H4. rewrite H4. reflexivity. all: try lia; auto.
Qed.

(** WRONG: cannot be done distinctly unfortunately *)
Theorem alma1 clock :
  forall e v v1 v2 res1 n,
  is_value v1 -> is_value v2 -> V_rel n v1 v2 -> (* this is needed, because v2 could be ill-formed *)
  eval clock (varsubst v v1 e) = Res res1 ->
  (exists res2 clock, eval clock (varsubst v v2 e) = Res res2).
Proof.
  induction clock; intros.
  * inversion H2.
  * destruct e.
    - simpl in H2. eexists. exists 1. reflexivity.
    - destruct (v0 =? v)%string eqn:EQ.
      + simpl varsubst in H2. rewrite EQ in H2.
        simpl. rewrite EQ. eapply is_value_eval in H0. eexists. eexists. exact H0.
      + simpl varsubst in *. rewrite EQ in *. inversion H2.
    - inversion H2.
    - simpl varsubst in *. break_match_hyp.
      + eexists. exists 1. reflexivity.
      + eexists. exists 1. reflexivity.
    - simpl varsubst in *. break_match_hyp.
      + eexists. exists 1. reflexivity.
      + eexists. exists 1. reflexivity.
    - simpl in H2. repeat break_match_hyp; try congruence.
      + eapply IHclock with (v2 := v2) in Heqr; auto.
        eapply alma1_list with (v2 := v2) in Heqr0; auto. destruct Heqr, H3, Heqr0, H4.
        exists x, (S (x0 + x2)). simpl. eapply bigger_clock in H3. eapply bigger_clock_list in H4.
        rewrite H3, H4.
Abort.




Theorem alma clock :
  forall e n v v1 v2 res1,
  is_value v1 -> is_value v2 -> V_rel n v1 v2 ->
  eval clock (varsubst v v1 e) = Res res1 ->
  exists res2, (exists clock, eval clock (varsubst v v2 e) = Res res2) /\ (exists n, V_rel n res1 res2).
Proof.
  induction clock; intros.
  * inversion H2.
  * destruct e; simpl.
    - inversion H2. subst. exists (ELit l). split. exists 1. reflexivity. destruct n. simpl. auto. exists 0. reflexivity. exists 0. reflexivity.
    - simpl. destruct (v0 =? v)%string eqn:EQ.
      + simpl varsubst in H2. rewrite EQ in H2.
        eapply is_value_eval in H as H'. rewrite H' in H2. inversion H2. subst.
        exists v2. split. exists 1. apply is_value_eval. auto. auto. exists n. auto.
      + simpl varsubst in H2. rewrite EQ in H2. inversion H2.
    - simpl in *. inversion H2.
    - simpl varsubst in H2. break_match_hyp.
      + simpl. simpl in H2. inversion H2. subst. exists (EFun vl e). split. exists 1.
        reflexivity.
        exists 0. reflexivity.
      + simpl in H2. inversion H2. subst. eexists. split. exists 1. reflexivity.
        (* 
         TODO: with existentials, we get stuck here
         
        epose (IHclock (varsubst_list vl vals2 e) n v v1 v2 _ H H0 H1 _). destruct e0, H3, H4.
        exists (S x0). simpl. constructor. auto. intros. constructor.
        ** admit.
        ** intros. destruct H8. destruct H3. (** some kind of commutativity needed here *)
          replace (varsubst_list vl vals1 (varsubst v v1 e)) with (varsubst v v1 (varsubst_list vl vals1 e)) in H8.
          replace (varsubst_list vl vals2 (varsubst v v2 e)) with (varsubst v v2 (varsubst_list vl vals2 e)) in H9.
          eapply bigger_clock in H3. eapply bigger_clock in H9. erewrite H3 in H9. *)
Admitted.

Corollary varsubst_indep_helper :
  forall b n v1 v2 var,
  E_rel (V_rel n) b b ->
  is_value v1 -> is_value v2 ->
  V_rel n v1 v2 ->
  (exists n, E_rel (V_rel n) (varsubst var v1 b) (varsubst var v2 b)).
Proof.
  intros. epose (alma _ _ _ _ _ _ _ H0 H1 H2).
  eexists.
  constructor.
  * split; intros.
    - destruct H3, H3. epose (alma _ _ _ _ _ _ _ H0 H1 H2 H3). destruct e, H4.
      eexists. exact H4.
    - destruct H3, H3. epose (alma _ _ _ _ _ _ _ H1 H0 (V_rel_sym _ _ _ H2) H3). destruct e, H4.
      eexists. exact H4.
  * intros. destruct H3.
    epose (alma _ _ _ _ _ _ _ H0 H1 H2 H3). destruct e, H5, H5.
    apply bigger_clock with (clock' := x0 + clock) in H5.
    apply bigger_clock with (clock' := x0 + clock) in H4. rewrite H4 in H5. inversion H5.
    subst. destruct H6. exact H6. auto. all: lia.
Qed.

Corollary varsubst_list_indep :
  forall vals1 vals2 n b vl,
  E_rel (V_rel n) b b -> 
  (forall i : nat,
     i < Datatypes.length vl -> V_rel n (nth i vals1 (ELit 0)) (nth i vals2 (ELit 0)))
->
  E_rel (V_rel n) (varsubst_list vl vals1 b) (varsubst_list vl vals2 b).
Proof.
  (* TODO, should be simple from varsubst_indep *)
Admitted.

Theorem V_Rel_refl n : (** Builds on the previous one *)
  forall x, is_value x -> V_rel n x x.
Proof.
  induction n; unfold Reflexive; intros.
  * simpl. auto.
  * simpl. destruct x; inversion H.
    - apply V_rel_num_refl.
    - subst. constructor. auto. intros.
Abort.

Lemma funsubst_indep :
  forall n f b e,
  E_rel (V_rel n) b b
->
  E_rel (V_rel n) (funsubst f e b) (funsubst f e b).
Proof.
  (* TODO *)
Admitted.

(** WARNING: use only for termination checking: *)
(*
Axiom ff : False.
*)

Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Goal let e := (EFun ["X"%string] (EFun ["Y"%string] (EVar "X"%string))) in Equiv_rel 1 e e.
Proof.
  constructor.
  * split; intros; auto.
  * intros. destruct H. destruct clock; inversion H. inversion H0. subst.
    simpl. constructor. auto. intros. eapply eq_sym, element_exist in H1 as H1'. destruct H1', H4. subst.
    intros. eapply eq_sym, element_exist in H2 as H2'. destruct H2', H4. subst.
    inversion H1. inversion H2. apply eq_sym, length_zero_iff_nil in H5. apply eq_sym, length_zero_iff_nil in H6. subst.
    constructor. split; intros. eexists. exists 1. simpl. reflexivity. eexists. exists 1. simpl. reflexivity.
    intros. destruct H4. unfold varsubst_list in *. simpl in H4, H5. destruct clock0; inversion H4.
    inversion H5. subst. (* TODO: stuck :( *)
Abort.

Theorem Equiv_rel_refl :
  forall x n, Equiv_rel n x x. (** TODO: does not hold, e.g. for fun(X) => fun(Y) => X and n = 1 
  
                                    countfuns??? or size as the decreasing argument?
  
  *)
Proof.
  induction x using Exp_ind2 with (Q := fun l => list_forall (fun e => forall n, Equiv_rel n e e) l); intros.
  * constructor. split; intros; auto.
    intros. destruct H. rewrite H in H0. inversion H0. subst.
    destruct clock. inversion H. simpl in H. inversion H. subst. destruct n; simpl. auto. constructor.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock; inversion H.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock; inversion H.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock; inversion H. inversion H0. subst.
    destruct n. simpl. auto.
    simpl. constructor. auto. intros. apply varsubst_list_indep. 
    apply IHx. apply H3.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock; inversion H. inversion H0. subst.
    destruct n. simpl. auto.
    simpl. constructor. auto. intros. apply varsubst_list_indep. apply funsubst_indep. apply IHx. apply H3.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock. inversion H. simpl in H, H0. break_match_hyp; try congruence.
    break_match_hyp; try congruence.
    - break_match_hyp; try congruence. break_match_hyp; try congruence.
      rewrite H in H0. inversion H0. subst. pose (IHx (S n)). destruct e0.
      specialize (H2 _ _ _ (conj Heqr Heqr)). simpl in H2. inversion H2. subst. apply Nat.eqb_eq in Heqb.
      pose (indexed_to_forall el (fun e : Exp => forall n : nat, Equiv_rel n e e) (ELit 0)).
      destruct i. specialize (H3 IHx0). clear H4.
      assert (forall i : nat,
     i < Datatypes.length v0 -> V_rel n (nth i v0 (ELit 0)) (nth i v0 (ELit 0))).
     {
       intros. apply list_eval_eq_length in Heqr0 as ll. rewrite ll in H3.
       specialize (H3 i H4 n). destruct H3. eapply H5. split; eapply all_eval_single in Heqr0.
       * exact Heqr0.
       * rewrite ll. auto.
       * exact Heqr0.
       * rewrite ll. auto.
     }
      rewrite Heqb in H4. specialize (H8 v0 v0 Heqb Heqb H4). inversion H8. eapply H7.
      split; exact H.
    - break_match_hyp; try congruence. break_match_hyp; try congruence.
      rewrite H in H0. inversion H0. subst. pose (IHx (S n)). destruct e0.
      specialize (H2 _ _ _ (conj Heqr Heqr)).
      pose (indexed_to_forall el (fun e : Exp => forall n : nat, Equiv_rel n e e) (ELit 0)).
      destruct i. specialize (H3 IHx0). clear H4.
      assert (forall i : nat,
     i < Datatypes.length v0 -> V_rel n (nth i v0 (ELit 0)) (nth i v0 (ELit 0))).
     {
       intros. apply list_eval_eq_length in Heqr0 as ll. rewrite ll in H3.
       specialize (H3 i H4 n). destruct H3. eapply H5. split; eapply all_eval_single in Heqr0.
       * exact Heqr0.
       * rewrite ll. auto.
       * exact Heqr0.
       * rewrite ll. auto.
     }
      apply Nat.eqb_eq in Heqb. rewrite Heqb in H4.
      simpl in H2. inversion H2. subst. specialize (H12 v0 v0 Heqb Heqb H4).
      destruct H12. eapply H6. split; exact H. 
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock. inversion H. simpl in H, H0.
    break_match_hyp; try congruence. rewrite H in H0. inversion H0. subst.
    pose (IHx1 n). destruct e. specialize (H2 _ _ _ (conj Heqr Heqr)).
    pose (IHx2 n). epose (varsubst_indep n _ _ _ _ e H2). destruct e0. eapply H4.
    split. exact H. exact H.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock. inversion H. simpl in H, H0.
    rewrite H in H0. inversion H0. subst. pose (IHx2 n). eapply funsubst_indep in e. destruct e.
    eapply H2. split. exact H. exact H.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock. inversion H. simpl in H, H0.
    repeat break_match_hyp; try congruence.
    rewrite H in H0. inversion H0. subst.
    destruct n. reflexivity. inversion H. subst.
    simpl. constructor.
  * constructor. split; intros; auto.
    intros. destruct H. destruct clock. inversion H. simpl in H, H0.
    repeat break_match_hyp; try congruence; subst;
    rewrite H in H0; inversion H0; subst.
    2-12: eapply IHx3; split; exact H; assumption.
    - eapply IHx2. split. exact H. assumption.
  * constructor. apply IHx. apply IHx0.
  * constructor.
Qed.






Definition Equiv_rel e1 e2 := exists n, E_rel (V_rel n) e1 e2.

Theorem Equiv_rel_refl :
  forall x, Equiv_rel x x.
Proof.
  intros. exists 0. constructor. simpl in H. subst.
  intros. exact H.
  intros. simpl in H. subst. exact H0.
Qed.


(*
Definition E_rel (V_rel : relation Exp) (e1 e2 : Exp) : Prop :=
 (*  ((terminating e1) <-> (terminating e2)) /\ *)
  (forall v1 v2, V_rel v1 v2 ->
    (exists clock, eval clock e1 = Res v1) <->
    (exists clock, eval clock e2 = Res v2))
.

Goal Equiv_rel (ELit 3) (sum 2).
Proof.
  exists 0. constructor; simpl in H; subst.
  intros. destruct H. destruct x; inversion H. subst.
  exists 100. simpl. auto.
  intros. destruct H. destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H.
  destruct x; inversion H. simpl in H. subst. exists 1. simpl. auto.
Qed.

(* Very hard to prove, because we need to guess v2 backwards :( *)
Goal Equiv_rel (EFun [] (ELit 3)) (EFun [] (sum 2)).
Proof.
  exists 1. constructor; simpl in H; intros; destruct H0.
  destruct x; inversion H0. subst. exists 2. simpl.
  destruct v2; try contradiction. inversion H. subst.
  apply eq_sym, length_zero_iff_nil in H4. subst. specialize (H6 [] [] eq_refl eq_refl).
  epose (H6 _). unfold varsubst_list in e. simpl in e. unfold E_rel in e. specialize (e (ELit 3) (ELit 3)).
  destruct e. reflexivity. *)
  

Definition related_exps : relation Exp :=
  fun e1 e2 =>
    forall cl1 cl2, G_rel cl1 cl2 ->
      E_rel (close cl1 e1) (close cl2 e2).

(* depends on E_rel symm *)
Lemma v_rel_refl n :
  Reflexive (V_rel n).
Proof.
  induction n.
  * unfold Reflexive. intros. simpl. auto.
  * unfold Reflexive in *. intros. destruct x.
    - simpl. apply V_rel_num_refl.
    - simpl. constructor. auto. intros. split.
      + admit. (* Equivalent environments *)
      + intros. destruct H2.
Abort.
(* Set Positivity Checking. *)

(* Fixpoint v_rel (v1 v2 : Value) : Prop :=
match m with
| Int => V_rel_refl v1 v2
| Fun a b => V_rel_fun (v_rel a) (v_rel b) v1 v2
end. *)

Fixpoint size (e : Exp) : nat :=
match e with
 | ELit l => 1
 | EVar v => 1
 | EFunId f => 1
 | EFun vl e => 1 + size e
 | ERecFun f vl e => 1 + size e
 | EApp exp l => 1 + size exp + fold_right (fun x acc => size x + acc) 0 l
 | ELet v e1 e2 => 1 + size e1 + size e2
 | ELetRec f vl b e => 1 + size b + size e
 | EPlus e1 e2 => 1 + size e1 + size e2
 | EIf e1 e2 e3 => 1 + size e1 + size e2 + size e3
end.

Definition val_size (v : Value) :=
match v with
| VLit _ => 1
| VFun _ _ e => 1 + size e
| VRecFun _ _ _ e => 1 + size e
end.

Definition val_rel_size : relation Value :=
  fun v1 v2 => V_rel (val_size v1 + val_size v2) v1 v2.




(* TODO: Here, we could say exists a nat, which is the parameter of v_rel, if needed *)
Definition eq_env : relation Env :=
 fun env env' =>
   forall (x : VarFunId), Environment.In x env -> .


Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.
End list_length_ind.


Section nat_lt_ind.
  Variable P : nat -> Prop.

  Hypothesis H : forall n, (forall n', n' < n -> P n') -> P n.

  Theorem nat_lt_ind : forall n, P n.
  Proof.
    assert (forall n n' : nat, n' <= n -> P n') as H_ind.
    { induction n; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. subst. inversion H0.
      - apply IHn. lia.
    }
    intros n.
    apply H_ind with (n := n).
    lia.
  Qed.
End nat_lt_ind.

Theorem eq_env_get :
  forall env env', eq_env env env'
->
  forall v val, get_value env v = Some val
->
  exists val', get_value env' v = Some val' /\ val_rel_size val val'.
Proof.
  induction env using list_length_ind.
  intros. destruct H0. destruct env, env'.
  * inversion H1.
  * inversion H1.
  * inversion H0.
  * destruct p. destruct (var_funid_eqb v s) eqn:P.
    - pose (H2 0 (Nat.lt_0_succ _)). destruct a. simpl in H3, H4.
      destruct p0. simpl in H4, H3. subst. simpl. rewrite P. eexists.
      split. reflexivity. simpl in H1. rewrite P in H1. inversion H1. subst. auto.
    - simpl. destruct p0. simpl in H1. pose (H2 0 (Nat.lt_0_succ _)). destruct a. simpl in H4. subst.
      rewrite P in *. apply H with (l := env).
      + simpl. lia.
      + split.
        ** inversion H0. lia.
        ** intros. Search lt S. pose (H2 (S i) (Lt.lt_n_S _ _ H4)). exact a.
      + auto.
Qed.

Theorem eq_env_get_none :
  forall env env', eq_env env env'
->
  forall v, get_value env v = None
->
  get_value env' v = None.
Proof.
(* Same proof as before *)
  induction env using list_length_ind.
  intros. destruct H0. destruct env, env'.
  * auto.
  * inversion H0.
  * inversion H0.
  * destruct p, p0. pose (H2 0 (Nat.lt_0_succ _)). destruct a. simpl in H3, H4. subst. 
    destruct (var_funid_eqb v s0) eqn:P.
    - simpl get_value in *. rewrite P in *. inversion H1.
    - simpl get_value in *. rewrite P in *. apply H with (l := env).
      + simpl. lia.
      + split.
        ** inversion H0. lia.
        ** intros. Search lt S. pose (H2 (S i) (Lt.lt_n_S _ _ H4)). exact a.
      + auto.
Qed.

Theorem eq_env_eval :
  forall clock e env env' v, eq_env env env'
->
  eval_env clock env e = Res v
->
  exists v', eval_env clock env' e = Res v' /\ val_rel_size v v'.
Proof.
  induction clock; intros.
  * inversion H0.
  * destruct e.
    - simpl in H0. inversion H0. eexists. simpl. split. reflexivity. constructor.
    - simpl in H0. break_match_hyp.
      + apply eq_env_get with (env' := env') in Heqo. 2: auto. simpl. destruct Heqo, H1. rewrite H1.
        exists x. inversion H0. subst. split. auto. auto.
      + apply eq_env_get_none with (env' := env') in Heqo. 2: auto. inversion H0.
    - simpl in H0. break_match_hyp.
      + apply eq_env_get with (env' := env') in Heqo. 2: auto. simpl. destruct Heqo, H1. rewrite H1.
        exists x. inversion H0. subst. split. auto. auto.
      + apply eq_env_get_none with (env' := env') in Heqo. 2: auto. inversion H0.
    - simpl in H0. inversion H0. subst. eexists. simpl. split. reflexivity.
      constructor.
      + auto.
      + intros. constructor. admit. admit.
        
    - simpl in H0. inversion H0. subst. eexists. simpl. split. reflexivity. constructor.
      + auto.
      + intros. constructor. admit. admit. (* this is problematic (endless recursive proof) -> finite unfolding *)
    - admit.
    
Admitted.

Corollary eq_env_term :
  forall env env' e, equiv_env env env' -> terminating e env -> terminating e env'.
Proof.
  intros. unfold terminating in *. destruct H0, H0. eapply equiv_env_eval in H0. 2: exact H. destruct H0, H0.
  eexists. exists x0. exact H0.
Qed.

(* TODO: maybe exists here can also help *)
Definition equiv_exp : Exp -> Exp -> Prop :=
  fun e1 e2 =>
  forall env env', eq_env env env'
 ->
  E_rel (v_rel (size e1 + size e2)) env env' e1 e2.

Section examples.

Goal
  equiv_exp (ELit 5) (EPlus (ELit 5) (ELit 0)).
Proof.
  unfold equiv_exp. intros.
  constructor.
  * prove_term.
  * intros. destruct H0, clock; inversion H0. destruct clock; inversion H1. repeat constructor.
Qed.

(* Lemma insert_value_comm :
forall env v1 v2 val1 val2, v1 <> v2 ->
  Permutation (insert_value (insert_value env v1 val1) v2 val2)
  (insert_value (insert_value env v2 val2) v1 val1).
Proof.
  induction env; intros.
  * simpl. apply var_funid_eqb_neq in H. rewrite H, (var_funid_eqb_sym _ _), H.
Qed. *)

Lemma swap_append_insert :
forall env vl vals v val v', NoDup vl -> length vl = length vals -> ~ In v vl ->
  get_value (append_vars_to_env vl vals (insert_value env (inl v) val)) v' =
  get_value (insert_value (append_vars_to_env vl vals env) (inl v) val) v'.
Proof.
  induction vl using list_length_ind.
  destruct vl, vals; intros.
  * simpl. auto.
  * inversion H1.
  * inversion H1.
  * inversion H0. subst. simpl. destruct (var_funid_eqb v' (inl v1)) eqn:P.
    - apply var_funid_eqb_eq in P. subst. rewrite get_value_here. 
Admitted.

Lemma eval_varlist :
forall x vl vals env, NoDup vl -> length vl = length vals ->
  eval_list (eval_env (S x) (append_vars_to_env vl vals env)) (map EVar vl) = Res vals.
Proof.
  induction vl using list_length_ind.
  destruct vals, vl; intros.
  * simpl. auto.
  * inversion H1.
  * inversion H1.
  * inversion H1. inversion H0. subst. remember (S x) as xx. simpl. rewrite Heqxx at 1. simpl. rewrite swap_append_insert. rewrite get_value_here. rewrite H. all: auto.
Qed.

Lemma insert_shadow env : forall v val1 val2,
  insert_value (insert_value env v val1) v val2 =
  insert_value env v val2.
Proof.
  induction env; intros.
  * simpl. rewrite var_funid_eqb_refl. auto.
  * simpl. destruct a. break_match_goal.
    - simpl. rewrite var_funid_eqb_refl. auto.
    - simpl. rewrite Heqb. rewrite IHenv. auto.
Qed.

Lemma append_shadow : forall vl env vals1 vals2,
  length vals1 = length vals2 ->
  append_vars_to_env vl vals1 (append_vars_to_env vl vals2 env) =
  append_vars_to_env vl vals1 env.
Proof.
  induction vl; intros.
  * simpl. destruct vals1, vals2; auto.
  * simpl. destruct vals1, vals2; auto.
    - inversion H.
Admitted.


Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.


Lemma eta_conversion X b :
  equiv_exp (EFun [X] b) (EFun [X] (EApp (EFun [X] b) [EVar X])).
Proof.
  unfold equiv_exp. intros. constructor.
  * prove_term.
  * intros. destruct H0, clock; inversion H0. inversion H1.
    constructor. auto. intros. constructor.
    - split; intros.
      + destruct H7, H7. symmetry in H2. apply element_exist in H2 as H2'.
        symmetry in H5. apply element_exist in H5 as H5'. destruct H2', H5', H8, H9. subst.
        inversion H2.
        inversion H5. apply eq_sym, length_zero_iff_nil in H4.
        apply eq_sym, length_zero_iff_nil in H8. subst. simpl append_vars_to_env in *.
        epose (H6 0 _). simpl in v.
        apply eq_env_eval with (env' := (insert_value env' (inl X) x2)) in H7. destruct H7, H3.
        exists x3. exists (S (S x0)).
        remember (S x0) as xx. simpl. rewrite Heqxx at 1. simpl.
        rewrite Heqxx at 1. simpl. rewrite get_value_here. rewrite insert_shadow. rewrite Heqxx.
        eapply bigger_clock in H3. exact H3. lia. admit. (* this is just techincal *)
      + admit. (* this is just techincal *)
    - intros. destruct H7.
      symmetry in H2. apply element_exist in H2 as H2'.
      symmetry in H5. apply element_exist in H5 as H5'. destruct H2', H5', H9, H10. subst.
      inversion H2.
      inversion H5. apply eq_sym, length_zero_iff_nil in H4.
      apply eq_sym, length_zero_iff_nil in H9. subst. simpl append_vars_to_env in *.
      epose (H6 0 _). simpl in v.
      destruct clock0. inversion H7. destruct clock0. inversion H8. remember (S clock0) as xx. simpl in H8.
      rewrite Heqxx in H8 at 1. simpl in H8.
      rewrite Heqxx in H8 at 1. simpl in H8. rewrite get_value_here in H8. rewrite insert_shadow in H8.
      apply bigger_clock with (clock' := S xx) in H8. simpl. rewrite H8 in H3. unfold val_rel_size in H4.
      simpl. inversion H3. subst. admit. (* TODO: fix val_rel_size *)
      lia. constructor. admit. admit. (* this is just techincal *)
     Unshelve. all: auto.
Admitted.

Goal
  equiv_exp (EFun [] (ELit 1)) (EFun [] (EPlus (ELit 0) (ELit 1))).
Proof.
  start_equiv. prove_term.
  intros. destruct H0. destruct clock; inversion H0. inversion H1. subst.
  constructor. intros. auto. simpl.
  intros. apply length_zero_iff_nil in H2. apply length_zero_iff_nil in H3. subst.
  constructor. prove_term.
  intros. destruct H2.
  destruct clock0; inversion H2. destruct clock0; inversion H3. constructor.
Qed.

Definition inf f := EApp (ERecFun f [] (EApp (EFunId f) [])) [].

Axiom alma : forall f clock env, eval_env clock env (inf f) = Timeout.

Goal forall f,
  ~ equiv_exp (ELit 0) (inf f).
Proof.
  unfold not. intros. unfold equiv_exp in H.
  epose (H [] [] _). inversion e. destruct H0.
  epose (H0 _). destruct t, H3. rewrite alma in H3. inversion H3.
  Unshelve. unfold eq_env. split. auto. intros. inversion H0.
  eexists. exists 1. reflexivity.
Qed.

Definition wrong_E_rel (V_rel : relation Value) (env env' : Environment) (e1 e2 : Exp) : Prop :=
  (forall clock v1 v2,
    eval_env clock env e1 = Res v1 /\
    eval_env clock env' e2 = Res v2 ->
    V_rel v1 v2)
.

Inductive wrong_V_rel_fun (valr : relation Value) : relation Value :=
| clos_rel21 vl env b vl' env' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> valr (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0))) ->
  wrong_E_rel valr (append_vars_to_env vl vals1 env) (append_vars_to_env vl' vals2 env') b b')
->
  wrong_V_rel_fun valr (VFun env vl b) (VFun env' vl' b')
(** TODO: recfun *)
| rec_clos_rel21 f vl env b f' vl' env' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> valr (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0))) ->
  wrong_E_rel valr (append_vars_to_env vl vals1 (insert_value env (inr f) (VRecFun env f vl b)))
             (append_vars_to_env vl' vals2 (insert_value env' (inr f) (VRecFun env' f' vl' b'))) b b')
->
  wrong_V_rel_fun valr (VRecFun env f vl b) (VRecFun env' f' vl' b')
.

Fixpoint wrong_v_rel (n : nat) : relation Value :=
fun v1 v2 =>
match n with
| 0 => False
| S n' =>
  match v1, v2 with
  | VLit _, VLit _ => V_rel_refl v1 v2
  | VFun _ _ _, VFun _ _ _ => wrong_V_rel_fun (wrong_v_rel n') v1 v2
  | VRecFun _ _ _ _, VRecFun _ _ _ _ => wrong_V_rel_fun (wrong_v_rel n') v1 v2
  | _, _ => False
  end
end.

Definition wrong_val_rel_size : relation Value :=
  fun v1 v2 => wrong_v_rel (val_size v1 + val_size v2) v1 v2.

Definition wrong_eq_env : relation Environment :=
 fun env env' =>
  length env = length env' /\
  forall i, i < length env -> wrong_val_rel_size (snd (nth i env (inl "X"%string, VLit 0))) (snd (nth i env' (inl "X"%string, VLit 0))) /\ fst (nth i env (inl "X"%string, VLit 0)) = fst (nth i env' (inl "X"%string, VLit 0)).

Definition wrong_equiv_exp : Exp -> Exp -> Prop :=
  fun e1 e2 =>
  forall env env', eq_env env env'
 ->
  wrong_E_rel (v_rel (size e1 + size e2)) env env' e1 e2.

Goal forall f,
  wrong_equiv_exp (ELit 0) (inf f).
Proof.
  unfold wrong_equiv_exp. intros. unfold wrong_E_rel. intros. destruct H0.
  rewrite alma in H1. inversion H1.
Qed.


End examples.

(* compatibility lemmas: *)

Lemma compat_lit l : equiv_exp (ELit l) (ELit l).
Proof.
  constructor. prove_term.
  * intros. destruct H0. destruct clock; inversion H0. inversion H1. constructor.
Qed.

Lemma compat_var v : equiv_exp (EVar v) (EVar v).
Proof.
  constructor.
  * destruct (get_value env (inl v)) eqn:P.
    - split; intros; destruct H0, H0, x0; inversion H0.
      + rewrite P in H2. inversion H2. subst. eexists. exists (S x0). simpl.
        

(*
(** Values at base type are V-related exactly when they are identical *)
Definition V_rel_real : relation (val ℝ) := eq. *)

(*
(** Values at arrow type are V-related when they take V-related inputs to
    E-related outputs. *)
Inductive V_rel_arrow τa τr
          (V_rel_a : relation (val τa))
          (V_rel_r : relation (val τr))
  : relation (val (τa ~> τr)) :=
| mk_V_rel_arrow (body0 body1 : expr (τa :: ·) τr) :
    (forall (va0 va1 : val τa),
        V_rel_a va0 va1 ->
        E_rel' τr V_rel_r
               (proj1_sig (ty_subst1 body0 va0))
               (proj1_sig (ty_subst1 body1 va1))) ->
      V_rel_arrow τa τr V_rel_a V_rel_r
                  (v_lam body0)
                  (v_lam body1).
Arguments mk_V_rel_arrow {_ _ _ _ _ _} Hva.

(** [V_rel] can't be defined as an inductive without angering the positivity
    checker. Instead, it is defined in pieces by type, then assembled by
    fixpoint. *)
Fixpoint V_rel τ : relation (val τ) :=
  match τ with
  | ℝ => V_rel_real
  | τa ~> τr => V_rel_arrow τa τr (V_rel τa) (V_rel τr)
  end.


*)



