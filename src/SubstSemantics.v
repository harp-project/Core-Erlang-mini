Require Export Scoping.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Export PeanoNat.
(* Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FSets.FMapFacts. *)

Import ListNotations.

Inductive ResultType {T : Set} : Set :=
| Timeout
| Fail
| Res (v : T)
.

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
         | EVar n v => Fail
         | EFunId n f => Fail
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
                                 then eval n e.[list_subst vals idsubst]
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res (ERecFun f vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Res vals => 
                                 if length vals =? length vl
                                 then eval n e.[list_subst (ERecFun f vl e::vals) idsubst]
                                 else Fail
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res _ => Fail
                         | r => r
                         end
         | ELet v e1 e2 => match eval n e1 with
                           | Res val => eval n e2.[val/]
                           | r      => r
                           end
         | ELetRec f vl b e => eval n e.[ERecFun f vl b/]
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
  Forall P l
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

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_app_start v hd tl xs (H : is_value v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v H tl [] empty_is_value)::xs, hd⟩

| red_app_fin xs e :
  ⟨ (FApp1 [])::xs, EFun [] e ⟩ --> ⟨ xs, e ⟩

| red_rec_app_fin xs e f :
  ⟨ (FApp1 [])::xs, ERecFun f [] e ⟩ --> ⟨ xs, e.[ERecFun f [] e/] ⟩

| app2_step v H hd tl vs H2 xs v' (H' : is_value v') :
  ⟨ (FApp2 v H (hd::tl) vs H2) :: xs, v' ⟩ --> ⟨ (FApp2 v H tl (vs ++ [v']) (step_value vs v' H2 H')) :: xs, hd ⟩

| red_app2 vl e vs v xs H H2 : 
  is_value v -> length vl = S (length vs) ->
  ⟨ (FApp2 (EFun vl e) H [] vs H2) :: xs, v ⟩ --> ⟨ xs, e.[list_subst (vs ++ [v]) idsubst] ⟩

| red_rec_app2 vl f e vs v xs H H2 : 
  is_value v -> length vl = S (length vs) ->
  ⟨ (FApp2 (ERecFun f vl e) H [] vs H2) :: xs, v ⟩ --> ⟨ xs,  e.[list_subst (ERecFun f vl e :: (vs ++ [v])) idsubst] ⟩

| red_let val e2 xs (H : is_value val) : ⟨ (FLet e2)::xs, val ⟩ --> ⟨ xs, e2.[val/] ⟩

| red_if_true e2 e3 xs : ⟨ (FIf e2 e3)::xs, ELit 0 ⟩ --> ⟨ xs, e2 ⟩

| red_if_false e2 e3 v xs (H : is_value v) :
  v <> ELit 0 ->
  ⟨ (FIf e2 e3)::xs, v ⟩ --> ⟨ xs, e3 ⟩

| red_plus_left e2 xs v (H : is_value v): ⟨ (FPlus1 e2)::xs, v ⟩ --> ⟨ (FPlus2 v H)::xs, e2 ⟩

| red_plus_right xs n m P :
   ⟨ (FPlus2 (ELit n) P)::xs, (ELit m) ⟩ --> ⟨ xs, ELit (n + m) ⟩ 

| red_letrec xs f vl b e:
  ⟨ xs, ELetRec f vl b e ⟩ --> ⟨ xs, e.[ERecFun f vl b/] ⟩

(** Steps *)
| step_let xs v e1 e2 : ⟨ xs, ELet v e1 e2 ⟩ --> ⟨ (FLet e2)::xs, e1 ⟩
| step_app xs e el: ⟨ xs, EApp e el ⟩ --> ⟨ (FApp1 el)::xs, e ⟩
| step_plus xs e1 e2 : ⟨ xs, EPlus e1 e2⟩ --> ⟨ (FPlus1 e2)::xs, e1⟩
| step_if xs e1 e2 e3 : ⟨ xs, EIf e1 e2 e3⟩ --> ⟨ (FIf e2 e3)::xs, e1⟩
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Exp -> nat -> FrameStack -> Exp -> Prop :=
| step_refl e : is_value e -> ⟨ [], e ⟩ -[ 0 ]-> ⟨ [], e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').

Definition eval_star (fs : FrameStack) (e : Exp) (v : Exp) : Prop :=
  exists k, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.

Notation "⟨ fs , e ⟩ -->* v" := (eval_star fs e v) (at level 50).

Goal ⟨ [], inc 1 ⟩ -->* ELit 2.
Proof.
  repeat econstructor.
  Unshelve. cbn. constructor.
Qed.

Goal ⟨ [], simplefun 10 ⟩ -->* ELit 10.
Proof.
  repeat econstructor.
Qed.

Goal ⟨ [], simplefun2 10 10 ⟩ -->* ELit 20.
Proof.
  unfold simplefun2.
  repeat econstructor.
  Unshelve.
  all : try constructor.
Qed.

Goal ⟨ [], sum 1 ⟩ -->* ELit 1.
Proof.
  unfold sum.
  simpl.
  econstructor.
  econstructor.
  econstructor.
  econstructor. constructor. cbn. econstructor. constructor. econstructor.
  eapply red_rec_app2. constructor.
  simpl. econstructor. econstructor. eapply step_if.
  econstructor. eapply red_if_false. constructor. cbn. congruence.
  econstructor. eapply step_plus.
  econstructor. eapply red_plus_left.
  econstructor. eapply step_app.
  econstructor. eapply red_app_start.
  econstructor. (* At this point we could say that eapply red_rec_app2 !!! (However, 1 + -1 is NOT a value) <- smarter tactics are needed ! *)
  eapply step_plus.
(* repeat   econstructor. *)
  econstructor. eapply red_plus_left.
  econstructor. eapply red_plus_right. simpl Z.add.
  econstructor. eapply red_rec_app2. constructor.
  simpl. econstructor. econstructor. eapply step_if.
  econstructor. eapply red_if_true.
  econstructor. eapply red_plus_right.
  econstructor.
  
  (* repeat econstructor. *)
  Unshelve.
  all : constructor.
Qed.

Ltac proof_irr :=
match goal with
| [H1 : ?P, H2 : ?P |- _] => assert (H1 = H2) by apply proof_irrelevance; subst
end.
Ltac proof_irr_many := repeat proof_irr.

Theorem step_determinism {e e' fs fs'} :
  ⟨ fs, e ⟩ --> ⟨fs', e'⟩ ->
  (forall fs'' e'', ⟨fs, e⟩ --> ⟨fs'', e''⟩ -> fs'' = fs' /\ e'' = e').
Proof.
  intro H. induction H; intros.
  * inversion H0; subst; try inversion H; try (proof_irr; auto).
  * inversion H; subst. auto.
  * inversion H; subst. auto.
  * inversion H0; subst; try inversion H'; try (proof_irr_many; auto).
  * inversion H3; subst; try inversion H0; auto.
  * inversion H3; subst; auto; try inversion H0.
  * inversion H0; subst; auto; try inversion H.
  * inversion H; subst; auto. congruence.
  * inversion H1; subst; auto; try congruence; try inversion H.
  * inversion H0; subst; try inversion H; try (proof_irr; auto).
  * inversion H; subst. auto.
  * inversion H; subst; try inversion H0; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H; subst; try inversion H0; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H; subst; try inversion H0; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H; subst; try inversion H0; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H; subst; try inversion H0; try inversion H'; try inversion H1; try (proof_irr_many; auto).
Qed.

Theorem value_nostep v (H : is_value v) :
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  induction H; unfold not; intros; inversion H; inversion H0; inversion H1.
Qed.

Theorem step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩ -> is_value v
->
  (forall fs'' v', ⟨fs, e⟩ -[k]-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intro. dependent induction H; intros.
  * inversion H1; subst; auto.
  * inversion H2; subst. apply IHstep_rt; auto. eapply step_determinism in H; eauto. destruct H. subst. auto.
Qed.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FCLOSED F -> EXPCLOSED e
->
  FCLOSED F' /\ EXPCLOSED e'.
Proof.
  intros F e F' e' IH. induction IH; intros.
  * inversion H0. subst. inversion H4. subst. split; auto.
    constructor; auto. destruct v; inversion H; inversion H1; auto.
  * inversion H. inversion H0. subst. split; auto. inversion H5. exact H2.
  * inversion H. inversion H0. subst. split; auto. inversion H5. subst. cbn in H2.
    apply -> subst_preserves_scope_exp; eauto.
  * inversion H0. subst. inversion H8. subst. split; auto. constructor; auto.
    apply Forall_app. split; auto. constructor; auto. destruct v'; inversion H'; inversion H1; auto.
  * inversion H3. subst. split; auto. inversion H9.
    apply -> subst_preserves_scope_exp; eauto. subst.
    rewrite Nat.add_0_r. replace (length vl) with (length (vs ++ [v])).
    apply scoped_list_idsubst. apply Forall_app. split; auto. constructor; auto.
    destruct v; inversion H0; inversion H4; auto.
    rewrite app_length. rewrite H1. simpl. lia.
  * inversion H3. split. auto. subst. inversion H9.
    apply -> subst_preserves_scope_exp; eauto. subst.
    rewrite Nat.add_0_r. replace (S (length vl)) with (length (ERecFun f vl e :: vs ++ [v])).
    apply scoped_list_idsubst. constructor. auto. apply Forall_app. split; auto. constructor; auto.
    destruct v; inversion H0; inversion H4; auto. simpl. rewrite H1, app_length. simpl. lia.
  * inversion H0. subst. split; auto. apply -> subst_preserves_scope_exp; eauto.
    apply cons_scope; auto. destruct val; inversion H; inversion H1; auto.
  * inversion H. subst. split; auto.
  * inversion H1. subst. split; auto.
  * inversion H0; subst. split; auto. constructor.
    destruct v; inversion H; inversion H1; auto. auto.
  * inversion H. subst. split; auto. constructor. constructor.
  * split; auto. inversion H0. 2: inversion H1. apply -> subst_preserves_scope_exp; eauto.
    subst. apply cons_scope; auto. constructor. auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
Qed.


Definition terminates_sem (fs : FrameStack) (e : Exp) : Prop :=
  exists v, ⟨fs, e⟩ -->* v.

Definition terminates_in_k_sem (fs : FrameStack) (e : Exp) (k : nat) : Prop :=
  exists v, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.



Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Exp -> nat -> Prop :=

| term_value v : is_value v -> | [] , v | 0 ↓ (** TODO: empty stack + 0 steps? *)
| term_if_true fs e1 e2 k : | fs , e1 | k ↓ -> | (FIf e1 e2)::fs , ELit 0 | S k ↓
| term_if_false fs e1 e2 v k : is_value v -> v <> ELit 0 -> | fs , e2 | k ↓ -> | (FIf e1 e2)::fs , v | S k ↓
| term_plus_left e2 v fs (H : is_value v) k : | (FPlus2 v H)::fs , e2 | k ↓ -> | (FPlus1 e2)::fs, v | S k ↓
| term_plus_right n m fs H k : | fs , ELit (n + m) | k ↓ -> | (FPlus2 (ELit n) H )::fs, ELit m | S k ↓
| term_let_subst v e2 fs k : is_value v -> | fs, e2.[v/] | k ↓ -> | (FLet e2)::fs, v | S k ↓
| term_letrec_subst f vl b e fs k : | fs, e.[ERecFun f vl b/] | k ↓ -> | fs, ELetRec f vl b e | S k ↓
| term_app_start v hd tl (H : is_value v) fs k : 
  | (FApp2 v H tl [] empty_is_value)::fs, hd| k ↓ -> | (FApp1 (hd::tl))::fs, v | S k ↓
| term_app1 fs e k :  | fs, e | k ↓ -> | (FApp1 [])::fs, EFun [] e | S k ↓
| term_app1_rec f e fs k : | fs, e.[ERecFun f [] e/] | k ↓ -> | (FApp1 [])::fs, ERecFun f [] e | S k ↓
| term_app_step v v' H hd tl vs H2 (H' : is_value v') fs k :
  | (FApp2 v H tl (vs ++ [v']) (step_value vs v' H2 H'))::fs, hd | k ↓ -> | (FApp2 v H (hd::tl) vs H2)::fs , v' | S k ↓
| term_app2 v vl e vs fs H H2 k : 
  length vl = S (length vs) -> is_value v -> | fs, e.[list_subst (vs ++ [v]) idsubst] | k ↓ -> | (FApp2 (EFun vl e) H [] vs H2)::fs, v | S k ↓
| term_app2_rec v f vl e vs fs H H2 k :
  length vl = S (length vs) -> is_value v -> | fs, e.[list_subst (ERecFun f vl e  :: (vs ++ [v])) idsubst] | k ↓ 
-> | (FApp2 (ERecFun f vl e) H [] vs H2)::fs, v | S k ↓


| term_if e e1 e2 fs k : | (FIf e1 e2)::fs, e | k ↓ -> | fs, EIf e e1 e2 | S k ↓
| term_plus e1 e2 fs k : | (FPlus1 e2)::fs, e1 | k ↓ -> | fs, EPlus e1 e2 | S k ↓
| term_app e vs fs k : | (FApp1 vs)::fs, e | k ↓ -> | fs, EApp e vs | S k ↓
| term_let v e1 e2 fs k : | (FLet e2)::fs, e1 | k ↓ -> | fs, ELet v e1 e2 | S k ↓

where "| fs , e | k ↓" := (terminates_in_k fs e k).

Definition terminates (fs : FrameStack) (e : Exp) := exists n, | fs, e | n ↓.
Notation "| fs , e | ↓" := (terminates fs e) (at level 80).

Theorem terminates_in_k_eq_terminates_in_k_sem :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  induction k; intros.
  * split; intros.
    - inversion H. inversion H0. inversion H2. constructor. auto.
    - inversion H. subst. econstructor. constructor. eauto.
  * split; intros.
    {
      inversion H. clear H. inversion H0; subst.
      assert (terminates_in_k_sem fs' e' k). { econstructor. eauto. } apply IHk in H.
      clear H4 H0. inversion H1; subst; econstructor; eauto.
    }
    {
      inversion H; subst;
      match goal with
      | [ H0 : | _, _ | S k ↓, H1 : | _, _ | k ↓ |- _] => apply IHk in H1; inversion H1; econstructor; econstructor; eauto; constructor
      end. all: auto.
    }
Qed.

Corollary terminates_eq_terminates_sem :
  forall e fs, terminates_sem fs e <-> | fs, e | ↓.
Proof.
  split; intros; inversion H.
  * inversion H0. econstructor. apply terminates_in_k_eq_terminates_in_k_sem.
    econstructor. eauto.
  * apply terminates_in_k_eq_terminates_in_k_sem in H0. inversion H0. econstructor. econstructor. eauto.
Qed.

Theorem terminates_step :
  forall fs e, | fs, e | ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | ↓.
Proof.
  intros. apply terminates_eq_terminates_sem in H. destruct H, H. destruct x0.
  * inversion H. subst. apply value_nostep in H0; intuition.
  * inversion H. subst. apply (step_determinism H0) in H2. destruct H2. subst.
    assert (terminates_sem fs' e'). { eexists. eexists. eauto. } apply terminates_eq_terminates_sem in H1.
    auto.
Qed.



