Require Export Scoping.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Export Coq.Arith.Wf_nat.
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
         | EVar n => Fail
         | EFunId n => Fail
         | EFun vl e => Res (EFun vl e)
         | EApp exp l => match eval n exp with
                         (** In Core Erlang this check only happens later *)
                         | Res (EFun vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Res vals => 
                                 if length vals =? length vl
                                 then eval n e.[list_subst (EFun vl e::vals) idsubst]
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
         | ELetRec f vl b e => eval n e.[EFun vl b/]
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
    - break_match_hyp; inversion H1. break_match_hyp; try congruence.
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
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v (* H *) tl [] (* empty_is_value *))::xs, hd⟩

| red_app_fin xs e :
  ⟨ (FApp1 [])::xs, EFun [] e ⟩ --> ⟨ xs, e.[EFun [] e/] ⟩

| app2_step v (H : is_value v) hd tl vs (H2 : Forall is_value vs) xs v' (H' : is_value v') :
  ⟨ (FApp2 v (* H *) (hd::tl) vs (* H2 *)) :: xs, v' ⟩ --> ⟨ (FApp2 v (* H *) tl (vs ++ [v']) (* (step_value vs v' H2 H') *)) :: xs, hd ⟩

| red_app2 vl e vs v xs (H2 : Forall is_value vs) : 
  is_value v -> length vl = S (length vs) ->
  ⟨ (FApp2 (EFun vl e) (* H *) [] vs (* H2 *)) :: xs, v ⟩ --> ⟨ xs,  e.[list_subst (EFun vl e :: (vs ++ [v])) idsubst] ⟩

| red_let val e2 xs v (H : is_value val) : ⟨ (FLet v e2)::xs, val ⟩ --> ⟨ xs, e2.[val/] ⟩

| red_if_true e2 e3 xs : ⟨ (FIf e2 e3)::xs, ELit 0 ⟩ --> ⟨ xs, e2 ⟩

| red_if_false e2 e3 v xs (H : is_value v) :
  v <> ELit 0 ->
  ⟨ (FIf e2 e3)::xs, v ⟩ --> ⟨ xs, e3 ⟩

| red_plus_left e2 xs v (H : is_value v): ⟨ (FPlus1 e2)::xs, v ⟩ --> ⟨ (FPlus2 v (* H *))::xs, e2 ⟩

| red_plus_right xs n m :
   ⟨ (FPlus2 (ELit n) (* P *))::xs, (ELit m) ⟩ --> ⟨ xs, ELit (n + m) ⟩ 

| red_letrec xs f vl b e:
  ⟨ xs, ELetRec f vl b e ⟩ --> ⟨ xs, e.[EFun vl b/] ⟩

(** Steps *)
| step_let xs v e1 e2 : ⟨ xs, ELet v e1 e2 ⟩ --> ⟨ (FLet v e2)::xs, e1 ⟩
| step_app xs e el: ⟨ xs, EApp e el ⟩ --> ⟨ (FApp1 el)::xs, e ⟩
| step_plus xs e1 e2 : ⟨ xs, EPlus e1 e2⟩ --> ⟨ (FPlus1 e2)::xs, e1⟩
| step_if xs e1 e2 e3 : ⟨ xs, EIf e1 e2 e3⟩ --> ⟨ (FIf e2 e3)::xs, e1⟩
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Exp -> nat -> FrameStack -> Exp -> Prop :=
| step_refl e Fs : (* is_value e ->  *)⟨ Fs, e ⟩ -[ 0 ]-> ⟨ Fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').

Definition eval_star (fs : FrameStack) (e : Exp) (v : Exp) : Prop :=
  is_value v /\ exists k, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.

Notation "⟨ fs , e ⟩ -->* v" := (eval_star fs e v) (at level 50).

Goal ⟨ [], inc 1 ⟩ -->* ELit 2.
Proof.
  repeat econstructor.
(*   Unshelve. cbn. constructor. *)
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
  constructor. constructor. econstructor.
  econstructor.
  econstructor.
  econstructor. constructor. cbn. econstructor. constructor. econstructor.
  econstructor.
  eapply red_app2. constructor.
  simpl. econstructor. econstructor. econstructor. eapply step_if.
  econstructor. eapply red_if_false. constructor. cbn. congruence.
  econstructor. eapply step_plus.
  econstructor. eapply red_plus_left.
  econstructor. cbn. econstructor. eapply step_app.
  econstructor. eapply red_app_start.
  econstructor. econstructor.
  eapply step_plus.
(* repeat   econstructor. *)
  econstructor. eapply red_plus_left.
  econstructor. econstructor. eapply red_plus_right. simpl Z.add.
  econstructor. eapply red_app2. constructor.
  simpl. econstructor. econstructor. econstructor. eapply step_if.
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
  * inversion H0; subst; try inversion H'; try (proof_irr_many; auto).
  * inversion H1; subst; try inversion H; auto.
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
  * inversion H0; subst; auto.
  * inversion H2; subst. apply IHstep_rt; auto. eapply step_determinism in H; eauto. destruct H. subst. auto.
Qed.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FSCLOSED F -> EXPCLOSED e
->
  FSCLOSED F' /\ EXPCLOSED e'.
Proof.
  intros F e F' e' IH. induction IH; intros.
  * inversion H0. subst. inversion H4. inversion H3. subst. split; auto.
    constructor; auto. constructor; auto. destruct v; inversion H; inversion H1; auto.
  * inversion H. inversion H0. subst. split; auto. inversion H5. subst. cbn in H2.
    apply -> subst_preserves_scope_exp; eauto.
  * inversion H0. subst. inversion H5. inversion H9. subst. split; auto. constructor; auto.
    constructor; auto.
    apply Forall_app. split; auto. constructor; auto. destruct v'; inversion H'; inversion H1; auto.
  * inversion H1. inversion H6. split. auto. subst. inversion H11.
    apply -> subst_preserves_scope_exp; eauto. subst.
    rewrite Nat.add_0_r. replace (S (length vl)) with (length (EFun vl e :: vs ++ [v])).
    apply scoped_list_idsubst. constructor. auto. apply Forall_app. split; auto. constructor; auto.
    destruct v; inversion H; inversion H3; auto. simpl. rewrite H0, app_length. simpl. lia.
  * inversion H0. inversion H4. 
    subst. split; auto. apply -> subst_preserves_scope_exp; eauto.
    apply cons_scope; auto. destruct val; inversion H; inversion H1; auto.
  * inversion H. inversion H3. subst. split; auto.
  * inversion H1. inversion H5. subst. split; auto.
  * inversion H0. inversion H4; subst. split; auto. constructor; auto.
    constructor. destruct v; inversion H; inversion H1; auto.
  * inversion H. inversion H3. subst. split; auto. constructor. constructor.
  * split; auto. inversion H0. 2: inversion H1. apply -> subst_preserves_scope_exp; eauto.
    subst. apply cons_scope; auto. constructor. auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    now constructor.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto. now constructor.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto. now constructor.
Qed.

(* Theorem result_is_value_m (fs : FrameStack) (e v : Exp) m :
  ⟨ fs, e ⟩ -[m]-> ⟨[], v⟩ -> is_value v.
Proof.
  intros. induction H; auto.
Qed. *)

Theorem result_is_value_star (fs : FrameStack) (e v : Exp) :
  ⟨ fs, e ⟩ -->* v -> is_value v.
Proof.
  intros. destruct H. auto.
Qed.

Corollary step_rt_closedness : forall F e v,
   ⟨ F, e ⟩ -->* v -> FSCLOSED F -> EXPCLOSED e
->
  VALCLOSED v.
Proof.
  intros. destruct H, H2. induction H2.
  * destruct e; try inversion H; now inversion H1.
  * apply step_closedness in H2; auto. now apply IHstep_rt.
Qed.

Definition terminates_sem (fs : FrameStack) (e : Exp) : Prop :=
  exists v, ⟨fs, e⟩ -->* v.

Definition terminates_in_k_sem (fs : FrameStack) (e : Exp) (k : nat) : Prop :=
  exists v, ⟨fs, e⟩ -[k]-> ⟨[], v⟩ /\ is_value v.



Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Exp -> nat -> Prop :=

| term_value v : is_value v -> | [] , v | 0 ↓ (** TODO: empty stack + 0 steps? *)
| term_if_true fs e1 e2 k : | fs , e1 | k ↓ -> | (FIf e1 e2)::fs , ELit 0 | S k ↓
| term_if_false fs e1 e2 v k : is_value v -> v <> ELit 0 -> | fs , e2 | k ↓ -> | (FIf e1 e2)::fs , v | S k ↓
| term_plus_left e2 v fs (H : is_value v) k : | (FPlus2 v (* H *))::fs , e2 | k ↓ -> | (FPlus1 e2)::fs, v | S k ↓
| term_plus_right n m fs k : | fs , ELit (n + m) | k ↓ -> | (FPlus2 (ELit n) (* H *) )::fs, ELit m | S k ↓
| term_let_subst v e2 fs k x : is_value v -> | fs, e2.[v/] | k ↓ -> | (FLet x e2)::fs, v | S k ↓
| term_letrec_subst vl b e fs f k : | fs, e.[EFun vl b/] | k ↓ -> | fs, ELetRec f vl b e | S k ↓
| term_app_start v hd tl (H : is_value v) fs k : 
  | (FApp2 v (* H  *) tl [] (* empty_is_value *))::fs, hd| k ↓ -> | (FApp1 (hd::tl))::fs, v | S k ↓
| term_app1 e fs k : | fs, e.[EFun [] e/] | k ↓ -> | (FApp1 [])::fs, EFun [] e | S k ↓
| term_app_step v v' (H : is_value v) hd tl vs (H2 : Forall is_value vs) (H' : is_value v') fs k :
  | (FApp2 v (* H *) tl (vs ++ [v']) (* (step_value vs v' H2 H') *))::fs, hd | k ↓ -> | (FApp2 v (* H *) (hd::tl) vs (* H2 *))::fs , v' | S k ↓

| term_app2 v vl e vs fs (* H *) (H2 : Forall is_value vs) k :
  length vl = S (length vs) -> is_value v -> | fs, e.[list_subst (EFun vl e  :: (vs ++ [v])) idsubst] | k ↓ 
-> | (FApp2 (EFun vl e) (* H *) [] vs (* H2 *))::fs, v | S k ↓


| term_if e e1 e2 fs k : | (FIf e1 e2)::fs, e | k ↓ -> | fs, EIf e e1 e2 | S k ↓
| term_plus e1 e2 fs k : | (FPlus1 e2)::fs, e1 | k ↓ -> | fs, EPlus e1 e2 | S k ↓
| term_app e vs fs k : | (FApp1 vs)::fs, e | k ↓ -> | fs, EApp e vs | S k ↓
| term_let v e1 e2 fs k : | (FLet v e2)::fs, e1 | k ↓ -> | fs, ELet v e1 e2 | S k ↓

where "| fs , e | k ↓" := (terminates_in_k fs e k).

Definition terminates (fs : FrameStack) (e : Exp) := exists n, | fs, e | n ↓.
Notation "| fs , e | ↓" := (terminates fs e) (at level 80).

Theorem terminates_in_k_eq_terminates_in_k_sem :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  induction k; intros.
  * split; intros.
    - inversion H. inversion H0. inversion H1. now constructor.
    - inversion H. subst. econstructor. split. constructor. auto.
  * split; intros.
    {
      inversion H. clear H. inversion H0; inversion H; subst.
      assert (terminates_in_k_sem fs' e' k). { econstructor. eauto. } apply IHk in H2.
      clear H0. inversion H3; subst; econstructor; eauto.
    }
    {
      inversion H; subst. (* ;
      match goal with
      | [ H0 : | _, _ | S k ↓, H1 : | _, _ | k ↓ |- _] => 
         apply IHk in H1; destruct H1 as [e0 [H1e H1k]]; inversion H1e; subst (* econstructor; econstructor; eauto; constructor*)
      end. *)
      (* TODO: boiler plate... *)
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. eauto. auto.
      * apply IHk in H5. destruct H5, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H4. destruct H4, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H4. destruct H4, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H4. destruct H4, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H5. destruct H5, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H6. destruct H6, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H0.
        econstructor; split. econstructor. constructor. all: eauto.
    }
Qed.

Corollary terminates_eq_terminates_sem :
  forall e fs, terminates_sem fs e <-> | fs, e | ↓.
Proof.
  split; intros; inversion H.
  * destruct H0, H1. econstructor. apply terminates_in_k_eq_terminates_in_k_sem.
    econstructor. split; eauto.
  * apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0, H0. econstructor.
    split. eauto. econstructor. eauto.
Qed.

Theorem terminates_step :
  forall fs e, | fs, e | ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | ↓.
Proof.
  intros. apply terminates_eq_terminates_sem in H. destruct H, H, H1. destruct x0.
  * inversion H1. subst. apply value_nostep in H0; intuition.
  * inversion H1. subst. apply (step_determinism H0) in H3. destruct H3. subst.
    assert (terminates_sem fs' e'). { eexists. split. eauto. eexists. eauto. } apply terminates_eq_terminates_sem in H2.
    auto.
Qed.

Theorem terminates_step_2 :
  forall n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | n - 1↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem in H. destruct H. destruct n.
  * destruct H. inversion H. subst. apply value_nostep in H0; intuition.
  * destruct H.
    inversion H. subst. apply (step_determinism H0) in H3. destruct H3. subst.
    assert (exists y, ⟨ fs', e' ⟩ -[ n ]-> ⟨ [], y ⟩ /\ is_value y). { 
      eexists. eauto. }
    apply ex_intro in H6. apply terminates_in_k_eq_terminates_in_k_sem in H2.
    now rewrite Nat.sub_1_r.
Qed.

Corollary terminates_step_any :
  forall k fs e, | fs, e | ↓ -> forall fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩
->
  | fs', e' | ↓.
Proof.
  induction k; intros; inversion H0; subst; auto.
  apply terminates_step in H2; auto. apply IHk in H5; auto.
Qed.

Corollary terminates_step_any_2 :
  forall k n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩
->
  | fs', e' | n - k ↓.
Proof.
  induction k; intros; inversion H0; subst; auto.
  * rewrite Nat.sub_0_r. auto.
  * apply terminates_step_2 with (n := n) in H2; auto.
    eapply IHk in H5; auto. 2: exact H2. now replace (n - S k) with ((n - 1) - k) by lia.
Qed.

Theorem is_value_dec v :
  {is_value v} + {~is_value v}.
Proof.
  destruct v.
  1, 4: left; constructor.
  all: right; intro; inversion H.
Qed.

Theorem term_dec :
  forall k e Fs, | Fs, e | k ↓ \/ ~ | Fs, e | k ↓.
Proof.
  induction k using lt_wf_ind. intros.
  destruct k.
  * destruct Fs.
    - destruct e. 1, 4: left; do 2 constructor.
      all: right; intro; inversion H0; inversion H1.
    - right. intro. inversion H0.
  * destruct e.
    - destruct Fs. right. intro. inversion H0.
      destruct f.
      + destruct l0.
        ** right. intro. inversion H0.
        ** epose proof (H k ltac:(lia) e _). destruct H0.
           -- left. constructor. constructor. exact H0.
           -- right. intro. inversion H1. subst. contradiction.
      + destruct l1.
        ** destruct v.
           1-3, 5-9: right; intro; inversion H0.
           destruct (Nat.eq_dec (length vl) (S (length l2))).
           -- destruct (Forall_dec is_value is_value_dec l2).
              ++ epose proof (H k ltac:(lia) _ _). destruct H0.
                 *** left. constructor; auto. constructor. exact H0.
                 *** right. intro. inversion H1. contradiction.
              ++ right. intro. inversion H0. contradiction.
           -- right. intro. inversion H0. subst. contradiction.
        ** destruct (Forall_dec is_value is_value_dec l2).
           -- destruct (is_value_dec v).
              ++ epose proof (H k ltac:(lia) _ _). destruct H0.
                 *** left. constructor; auto. constructor. exact H0.
                 *** right. intro. inversion H1. contradiction.
              ++ right. intro. inversion H0. contradiction.
           -- right. intro. inversion H0. contradiction.
      + epose proof (H k ltac:(lia) _ _). destruct H0.
        ** left. constructor. constructor. exact H0.
        ** right. intro. inversion H1. contradiction.
      + epose proof (H k ltac:(lia) _ _). destruct H0.
        ** left. constructor. constructor. exact H0.
        ** right. intro. inversion H1. contradiction.
      + destruct v.
        2-9: right; intro; inversion H0.
        ** epose proof (H k ltac:(lia) _ _). destruct H0.
           -- left. constructor. exact H0.
           -- right. intro. inversion H1. contradiction.
      + destruct l.
        ** epose proof (H k ltac:(lia) _ _). destruct H0.
           -- left. constructor. exact H0.
           -- right. intro. inversion H1. contradiction. contradiction.
        ** epose proof (H k ltac:(lia) _ _). destruct H0.
           -- left. constructor. constructor. intro. inversion H1. exact H0.
           -- right. intro. inversion H1. contradiction.
        ** epose proof (H k ltac:(lia) _ _). destruct H0.
           -- left. constructor. constructor. intro. inversion H1. exact H0.
           -- right. intro. inversion H1. contradiction.
    - right. intro. inversion H0; inversion_is_value.
    - right. intro. inversion H0; inversion_is_value.
    - destruct Fs. right. intro. inversion H0.
      destruct f.
      + destruct l.
        ** destruct vl.
           -- epose proof (H k ltac:(lia) _ _). destruct H0.
              ++ left. constructor. exact H0.
              ++ right. intro. inversion H1. contradiction.
           -- right. intro. inversion H0.
        ** epose proof (H k ltac:(lia) _ _). destruct H0.
           -- left. constructor. constructor. exact H0.
           -- right. intro. inversion H1. subst. contradiction.
      + destruct l1.
        ** destruct v.
           1-3, 5-9: right; intro; inversion H0.
           destruct (Nat.eq_dec (length vl0) (S (length l2))).
           -- destruct (Forall_dec is_value is_value_dec l2).
              ++ epose proof (H k ltac:(lia) _ _). destruct H0.
                 *** left. constructor; auto. constructor. exact H0.
                 *** right. intro. inversion H1. contradiction.
              ++ right. intro. inversion H0. contradiction.
           -- right. intro. inversion H0. subst. contradiction.
        ** destruct (Forall_dec is_value is_value_dec l2).
           -- destruct (is_value_dec v).
              ++ epose proof (H k ltac:(lia) _ _). destruct H0.
                 *** left. constructor; auto. constructor. exact H0.
                 *** right. intro. inversion H1. contradiction.
              ++ right. intro. inversion H0. contradiction.
           -- right. intro. inversion H0. contradiction.
      + epose proof (H k ltac:(lia) _ _). destruct H0.
        ** left. constructor. constructor. exact H0.
        ** right. intro. inversion H1. contradiction.
      + epose proof (H k ltac:(lia) _ _). destruct H0.
        ** left. constructor. constructor. exact H0.
        ** right. intro. inversion H1. contradiction.
      + right. intro. inversion H0.
      + epose proof (H k ltac:(lia) _ _). destruct H0.
        ** left. constructor. constructor. congruence. exact H0.
        ** right. intro. inversion H1. contradiction.
    - epose proof (H k ltac:(lia) _ _). destruct H0.
      + left. constructor. exact H0.
      + right. intro. inversion H1; try inversion_is_value. contradiction.
    - epose proof (H k ltac:(lia) _ _). destruct H0.
      + left. constructor. exact H0.
      + right. intro. inversion H1; try inversion_is_value. contradiction.
    - epose proof (H k ltac:(lia) _ _). destruct H0.
      + left. constructor. exact H0.
      + right. intro. inversion H1; try inversion_is_value. contradiction.
    - epose proof (H k ltac:(lia) _ _). destruct H0.
      + left. constructor. exact H0.
      + right. intro. inversion H1; try inversion_is_value. contradiction.
    - epose proof (H k ltac:(lia) _ _). destruct H0.
      + left. constructor. exact H0.
      + right. intro. inversion H1; try inversion_is_value. contradiction.
Qed.

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FApp1 l => EApp e l
 | FApp2 v l1 l2 => EApp v (l2 ++ [e] ++ l1)
 | FLet v e2 => ELet v e e2
 | FPlus1 e2 => EPlus e e2
 | FPlus2 v => EPlus v e
 | FIf e2 e3 => EIf e e2 e3
end.

Corollary transitive_eval : forall n  Fs Fs' e e',
  ⟨ Fs, e ⟩ -[n]-> ⟨ Fs', e' ⟩ -> forall n' Fs'' e'', ⟨ Fs', e' ⟩ -[n']-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs, e ⟩ -[n + n']-> ⟨ Fs'', e''⟩.
Proof.
  intros n Fs F' e e' IH. induction IH; intros; auto.
  simpl. econstructor. exact H. now apply IHIH.
Qed.

Corollary term_step_term :
  forall k n fs e fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | n - k ↓ -> n >= k 
->
  | fs, e | n ↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem.
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0, H0.
  pose proof (transitive_eval _ _ _ _ _ H _ _ _ H0). replace (k+(n-k)) with n in H3 by lia.
  eexists. eauto.
Qed.

Lemma eval_app_partial :
  forall vals vl e v Fs hds, length vl = length (hds ++ v :: vals) ->
  Forall is_value vals -> Forall is_value hds -> is_value v ->
  ⟨ FApp2 (EFun vl e) vals hds :: Fs, v ⟩ -[S (length vals)]-> ⟨ Fs , e.[list_subst (EFun vl e :: (hds ++ v :: vals)) idsubst]⟩.
Proof.
  induction vals; intros.
  * simpl. econstructor. constructor; auto. rewrite app_length in H. simpl in H. lia.
    constructor.
  * simpl. econstructor. constructor; auto. constructor. inversion H0. subst.
    epose proof (IHvals vl e a _ (hds ++ [v]) _ H6 _ H5). rewrite <- app_assoc in H3.
    exact H3.
  Unshelve.
    rewrite <- app_assoc. auto. apply Forall_app. split. auto. constructor; auto.
Qed.

Lemma eval_app_partial_core :
  forall hds' vals vl e e' v Fs hds, (* length vl = length (hds ++ v::hds' ++ vals) -> *)
  Forall is_value hds -> Forall is_value hds' -> is_value v ->
  ⟨ FApp2 (EFun vl e) (hds' ++ e' :: vals) hds :: Fs, v ⟩ -[S (length hds')]-> 
  ⟨ FApp2 (EFun vl e) vals (hds ++ v :: hds') :: Fs , e'⟩.
Proof.
  induction hds'; intros.
  * simpl. econstructor. constructor; auto. constructor.
    constructor.
  * simpl. econstructor. constructor; auto. constructor. inversion H0. subst.
    epose proof (IHhds' vals vl e _ a Fs (hds ++ [v]) _ _ H4).
    rewrite <- app_assoc in H2. exact H2.
  Unshelve.
    apply Forall_app. split; auto. auto.
Qed.

Theorem transitive_eval_rev : forall Fs Fs' e e' k1,
  ⟨ Fs, e ⟩ -[k1]-> ⟨ Fs', e' ⟩-> 
  forall Fs'' e'' k2,
  ⟨ Fs, e ⟩ -[k1 + k2]-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs', e' ⟩ -[k2]-> ⟨ Fs'', e'' ⟩.
Proof.
  intros Fs Fs' e e' k1 IH. induction IH; intros.
  * simpl in H. auto.
  * simpl in H0. inversion H0; subst. eapply step_determinism in H.
    2: exact H2. destruct H; subst.
    apply IHIH in H5. auto.
Qed.

Theorem app_term_fun : forall tl k hds e e' Fs,
  | FApp2 e' tl hds :: Fs, e | k ↓ -> Forall is_value hds ->
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), is_value v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩)
->
  exists vl b, e' = EFun vl b /\ length vl = S (length (hds ++ tl)).
Proof.
  induction tl; intros.
  * apply H1 in H as H'. 2: lia. destruct H', H2, H2.
    eapply terminates_step_any_2 in H. 2: exact H3.
    inversion H; subst; try inversion_is_value.
    rewrite app_length, Nat.add_0_r. do 2 eexists. split. reflexivity. auto.
  * apply H1 in H as H'. 2: lia. destruct H', H2, H2.
    eapply terminates_step_any_2 in H. 2: exact H3.
    inversion H; subst; try inversion_is_value.
    apply H1 in H13 as H''. 2: lia. destruct H'', H4, H4.
    eapply terminates_step_any_2 in H13. 2: exact H5.
    apply IHtl in H13. destruct H13, H6, H6. subst. exists x3, x4. split; auto.
    repeat rewrite app_length in *. simpl in *. lia.
    apply Forall_app; auto.
    intros. eapply H1. 2: exact H7. lia.
Qed.

Theorem frame_indep_step : forall e F F' Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ F' :: Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ F' :: Fs', e' ⟩.
Proof.
  intros. revert Fs'. dependent induction H; intros.
  all: try constructor; auto.
  all: try (apply cons_neq in x; contradiction).
  all: symmetry in x; try (apply cons_neq in x; contradiction).
Qed.

Theorem frame_indep_red : forall e F Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ Fs', e' ⟩.
Proof.
  intros. revert Fs'. dependent induction H; intros.
  all: try constructor; auto.
  all: symmetry in x; try (apply cons_neq_2 in x; contradiction).
  all: (apply eq_sym, cons_neq in x; contradiction).
Qed.

Theorem frame_indep_any : forall k e e' front front' Fs,
  ⟨ front ++ Fs, e ⟩ -[k]-> ⟨ front' ++ Fs, e' ⟩
->
  forall Fs', ⟨ front ++ Fs', e ⟩ -[k]-> ⟨ front' ++ Fs', e' ⟩.
Proof.
  induction k; intros.
  * inversion H; subst. apply app_inv_tail in H2. subst. now constructor.
  * inversion H; subst. inversion H1; subst.
    - 
Admitted.

Theorem frame_indep : forall k e Fs v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩
->
  forall Fs', ⟨ Fs', e ⟩ -[k]-> ⟨ Fs', v ⟩.
Proof.
  intros. epose proof (frame_indep_any k e v [] [] Fs H Fs').
  apply H0.
Qed.

Lemma eval_dec : forall Fs e,
  (exists v k, ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ is_value v)
  \/
  ~(exists v k, ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ is_value v).
Proof.
  intros.
Qed.

(* Lemma eval_app_steps : forall tl k hds x0 e x Fs,
  ⟨ FApp2 x0 tl hds :: Fs, e ⟩ -[ k ]-> ⟨ Fs, x ⟩
->
  k > length tl.
Proof.
  induction tl; intros. 
  * inversion H. subst. apply cons_neq in H3. contradiction. simpl. lia.
  * pose proof (eval_dec (FApp2 x0 (a :: tl) hds :: Fs) e (FApp2 x0 (a :: tl) hds :: Fs)).
Admitted. *)

(* Lemma term_eval_app_2 : forall tl hds x0 k e Fs (P : Forall is_value hds),
  is_value x0 -> | FApp2 x0 tl hds :: Fs, e | k ↓ ->
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), is_value v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩ /\ k <= m)
->
  exists (v : Exp) (k0 : nat),
    is_value v /\ ⟨ Fs, EApp x0 (hds ++ e :: tl) ⟩ -[ k0 ]-> ⟨ Fs, v ⟩ /\ k0 <= S (S k).
Proof.
  induction tl; intros.
  * apply H1 in H0 as H0'; auto. destruct H0', H2, H2, H3.
    eapply (terminates_step_any_2 _ _ _ _ H0) in H3 as H3'.
    inversion H3'; subst; try inversion_is_value.
    apply H1 in H13 as H0'; auto. destruct H0', H5, H5, H6. 2: lia.
    destruct hds.
    - exists x0, (2 + x1 + (S x2)). split; auto. split.
      econstructor. constructor. econstructor. simpl. constructor. constructor.
      eapply transitive_eval; eauto. econstructor. constructor; auto. auto. lia.
    - inversion H9. subst.
      epose proof (eval_app_partial_core hds [] vl e0 e e1 Fs [] ltac:(auto) H16 H15).
      pose proof (transitive_eval _ _ _ _ _ H10 _ _ _ H3).
      exists x0, (3 + (S (length hds) + x1 + x2)).
      split. auto. split.
      econstructor. constructor. econstructor. simpl. constructor. constructor.
      replace (S (S (length hds) + x1 + x2)) with ((S (length hds) + x1) + (1 + x2)) by lia.
      eapply transitive_eval. exact H14. econstructor. constructor; auto. auto.
      lia.
  * apply H1 in H0 as H0'. destruct H0', H2, H2.
    eapply (terminates_step_any_2 _ _ _ _ H0) in H3 as H3'.
    inversion H3'; subst; try inversion_is_value. 2: lia.
    
    assert (| FApp2 x0 tl (hds ++ [x]) :: Fs, a | k0 ↓) as PP. { auto. }

    apply IHtl in H13; auto.
    - destruct H13, H4, H4.
      inversion H5; subst; try inversion_is_value. inversion H6; subst; try inversion_is_value. inversion H7; subst. apply cons_neq in H14. contradiction.
      inversion H8; subst; try inversion_is_value. 2: { destruct hds; inversion H14. }
      (* inversion H10. admit.
      epose proof (eval_app_partial_core hds (a :: tl) vl e0 e x Fs [] _ ltac:(auto) H12 H'). *)
      
      (* exists x2, (2 + (x1 + k2)). split. auto.
      econstructor. constructor. *) destruct hds.
      + exists x2, (2 + (x1 + k2)). split. auto.
        econstructor. constructor.
        econstructor. apply red_app_start; auto. simpl in H13. inversion H13. subst.
        now epose (transitive_eval _ _ _ _ _ H3 _ _ _ H9).
      + simpl. simpl in H13. inversion H13. subst.
        
        (* exists x2, (2 + (x1 + k2)). split. auto.
        econstructor. constructor. *)
        
        (* econstructor. apply red_app_start; auto.  *)inversion H12. subst.
        inversion H18.
        ** apply app_term_fun in H0; auto. subst. destruct H0, H0, H0. congruence.
        ** subst.
           epose proof (eval_app_partial_core hds (a :: tl) vl e1 e e0 Fs []
                         ltac:(auto) H17 H16).
           epose proof (transitive_eval _ _ _ _ _ H14 _ _ _ H3).
           assert (⟨ FApp2 (EFun vl e1) (a :: tl) (e0 :: hds) :: Fs, x ⟩ -[1]->
                   ⟨ FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs, a ⟩).
           { econstructor. constructor; auto. constructor. }
           epose proof (transitive_eval _ _ _ _ _ H15 _ _ _ H19).
           epose proof (eval_app_partial_core hds (a :: tl) vl e1 x e0 Fs []
                         ltac:(auto) H17 H16).
           assert (exists j, k2 = S (Datatypes.length hds) + j). {
              admit.
           }
           destruct H22. subst. rewrite <- app_assoc in H9. simpl in H9.
           epose proof (transitive_eval_rev _ _ _ _ _ H21 _ _ _ H9).
           simpl in H21, H22.
           epose proof (transitive_eval _ _ _ _ _ H21 _ _ _ H19).
           Search (FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs).
           inversion H22; subst. apply cons_neq in H27. contradiction.
           inversion H24; subst; try inversion_is_value.
           rewrite <- app_comm_cons in H25.
           Search (FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs) e'.
           
           epose proof (transitive_eval _ _ _ _ _ H20 _ _ _ H25).
           
           exists x2, (2 + (S (Datatypes.length hds) + x1 + 1 + k1 )). split. auto.
           econstructor. constructor. econstructor. apply red_app_start; auto.
           exact H26.
    - apply Forall_app. split; auto.
    - intros. eapply H1. 2: exact H5. lia.
Unshelve.
  all: simpl; repeat rewrite app_length; simpl; try lia.
Admitted. *)

Lemma term_eval_app : forall tl hds x0 k e Fs (P : Forall is_value hds),
  is_value x0 -> | FApp2 x0 tl hds :: Fs, e | k ↓ ->
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), is_value v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩)
->
  exists (v : Exp) (k0 : nat),
    is_value v /\ ⟨ Fs, EApp x0 (hds ++ e :: tl) ⟩ -[ k0 ]-> ⟨ Fs, v ⟩.
Proof.
  induction tl; intros.
  * apply H1 in H0 as H0'; auto. destruct H0', H2, H2.
    eapply (terminates_step_any_2 _ _ _ _ H0) in H3 as H3'.
    inversion H3'; subst; try inversion_is_value.
    apply H1 in H12 as H0'; auto. destruct H0', H4, H4. 2: lia.
    destruct hds.
    - exists x0, (2 + x1 + (S x2)). split; auto.
      econstructor. constructor. econstructor. simpl. constructor. constructor.
      eapply transitive_eval; eauto. econstructor. constructor; auto. auto.
    - inversion H8. subst.
      epose proof (eval_app_partial_core hds [] vl e0 e e1 Fs [] ltac:(auto) H14 H13).
      pose proof (transitive_eval _ _ _ _ _ H6 _ _ _ H3).
      exists x0, (3 + (S (length hds) + x1 + x2)).
      split. auto.
      econstructor. constructor. econstructor. simpl. constructor. constructor.
      replace (S (S (length hds) + x1 + x2)) with ((S (length hds) + x1) + (1 + x2)) by lia. 
      eapply transitive_eval. exact H9. econstructor. constructor; auto. auto.
  * apply H1 in H0 as H0'. destruct H0', H2, H2.
    eapply (terminates_step_any_2 _ _ _ _ H0) in H3 as H3'.
    inversion H3'; subst; try inversion_is_value. 2: lia.
    
    assert (| FApp2 x0 tl (hds ++ [x]) :: Fs, a | k0 ↓) as PP. { auto. }

    apply IHtl in H13; auto.
    - destruct H13, H4, H4.
      inversion H5; subst; try inversion_is_value. inversion H6; subst; try inversion_is_value. inversion H7; subst. apply cons_neq in H14. contradiction.
      inversion H8; subst; try inversion_is_value. 2: { destruct hds; inversion H14. }
      (* inversion H10. admit.
      epose proof (eval_app_partial_core hds (a :: tl) vl e0 e x Fs [] _ ltac:(auto) H12 H'). *)
      
      (* exists x2, (2 + (x1 + k2)). split. auto.
      econstructor. constructor. *) destruct hds.
      + exists x2, (2 + (x1 + k2)). split. auto.
        econstructor. constructor.
        econstructor. apply red_app_start; auto. simpl in H13. inversion H13. subst.
        now epose (transitive_eval _ _ _ _ _ H3 _ _ _ H9).
      + simpl. simpl in H13. inversion H13. subst.
        
        (* exists x2, (2 + (x1 + k2)). split. auto.
        econstructor. constructor. *)
        
        (* econstructor. apply red_app_start; auto.  *)inversion H12. subst.
        inversion H18.
        ** apply app_term_fun in H0; auto. subst. destruct H0, H0, H0. congruence.
        ** subst.
           epose proof (eval_app_partial_core hds (a :: tl) vl e1 e e0 Fs []
                         ltac:(auto) H17 H16).
           epose proof (transitive_eval _ _ _ _ _ H14 _ _ _ H3).
           assert (⟨ FApp2 (EFun vl e1) (a :: tl) (e0 :: hds) :: Fs, x ⟩ -[1]->
                   ⟨ FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs, a ⟩).
           { econstructor. constructor; auto. constructor. }
           epose proof (transitive_eval _ _ _ _ _ H15 _ _ _ H19).
           epose proof (eval_app_partial_core hds (a :: tl) vl e1 x e0 Fs []
                         ltac:(auto) H17 H16).
           assert (exists j, k2 = S (Datatypes.length hds) + j). {
              Search k2.
              admit.
           }
           destruct H22. subst. rewrite <- app_assoc in H9. simpl in H9.
           epose proof (transitive_eval_rev _ _ _ _ _ H21 _ _ _ H9).
           simpl in H21, H22.
           epose proof (transitive_eval _ _ _ _ _ H21 _ _ _ H19).
           Search (FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs).
           inversion H22; subst. apply cons_neq in H27. contradiction.
           inversion H24; subst; try inversion_is_value.
           rewrite <- app_comm_cons in H25.
           Search (FApp2 (EFun vl e1) tl (e0 :: hds ++ [x]) :: Fs) e'.
           
           epose proof (transitive_eval _ _ _ _ _ H20 _ _ _ H25).
           
           exists x2, (2 + (S (Datatypes.length hds) + x1 + 1 + k1 )). split. auto.
           econstructor. constructor. econstructor. apply red_app_start; auto.
           exact H26.
    - apply Forall_app. split; auto.
    - intros. eapply H1. 2: exact H5. lia.
Unshelve.
  all: simpl; repeat rewrite app_length; simpl; try lia.
Admitted.

Theorem term_eval : forall x Fs e, | Fs, e | x ↓ ->
  exists v k, is_value v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ (* /\ k <= x *).
Proof.
  induction x using lt_wf_ind. destruct x; intros; inversion H0; subst; try congruence.
  * exists e, 0. now repeat constructor.
  * exists (ELit 0), 0. split; [ constructor | do 2 constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor].
  * exists (ELit m), 0. split; [ constructor | do 2 constructor].
  * exists e, 0. split; [ auto | now constructor].
  * apply H in H4. destruct H4, H1, H1. exists x0, (S x1).
    split; [ auto | ]. econstructor. constructor. auto. lia.
  * exists e, 0. split; [ auto | now constructor ].
  * exists (EFun [] e0), 0. split; [ constructor | do 2 constructor].
  * exists e, 0. split; [ auto | now constructor].
  * exists e, 0. split; [ auto | now constructor ].
  * apply H in H4 as HH. destruct HH, H1, H1. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    - apply H in H8. 2: lia. destruct H8, H3, H3.
      exists x0, (S (x1 + S x2)). split. auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor. auto.
    - apply H in H11. 2: lia. destruct H11, H3, H3.
      exists x2, (S (x1 + S x3)). split. auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor; auto. auto.
  * apply H in H4 as HH. destruct HH, H1, H1. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    apply H in H9 as HH. destruct HH, H3, H3. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H9) in H5 as H5'.
    inversion H5'; subst; try inversion_is_value.
    exists (ELit (n + m)), (S (x1 + (S (x3 + 1)))).
    split. constructor.
    econstructor. constructor. eapply transitive_eval; eauto. 
    econstructor. constructor; auto. eapply transitive_eval; eauto.
    econstructor. constructor. constructor.
  * apply H in H4 as v_eval. 2: lia. destruct v_eval, H1, H1.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    destruct vs.
    - inversion H2'; subst; try inversion_is_value.
      apply H in H7. 2: lia. destruct H7, H3, H3.
      exists x0, (S (x1 + S x2)). split; auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor. auto.
    - inversion H2'; subst; try inversion_is_value.
      epose proof (term_eval_app vs [] x0 k e Fs ltac:(auto) H8 H10 _).
      destruct H3, H3, H3, H5. inversion H5; subst; try inversion_is_value.
      inversion H7; subst; try inversion_is_value.
      inversion H11; subst. apply cons_neq in H15. contradiction.
      inversion H12; subst; try inversion_is_value.
      exists x2, (S (x1 + S k1)). split; auto.
      econstructor. constructor. eapply transitive_eval; eauto.
    Unshelve.
      intros. apply H with (m := m); eauto. lia.
  * apply H in H4 as HH. destruct HH, H1, H1. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    apply H in H10 as HH. destruct HH, H3, H3. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H10) in H5 as H5'.
    exists x2, (S (x1 + (S x3))).
    split. auto.
    econstructor. constructor. eapply transitive_eval; eauto. 
    econstructor. constructor; auto. auto.
Qed.

Theorem term_eval_2 : forall x Fs e, | Fs, e | x ↓ ->
  exists v k, is_value v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  induction x using lt_wf_ind. destruct x; intros; inversion H0; subst; try congruence.
  * exists e, 0. now repeat constructor.
  * exists (ELit 0), 0. split; [ constructor | do 2 constructor ]. lia.
  * exists e, 0. split; [ auto | split; [now constructor | lia ] ].
  * exists e, 0. split; [ auto | split; [ now constructor | lia ] ].
  * exists (ELit m), 0. split; [ constructor | do 2 constructor]. lia.
  * exists e, 0. split; [ auto | split; [now constructor | lia] ].
  * apply H in H4. destruct H4, H1, H1. exists x0, (S x1).
    split; [ auto | ]. split. econstructor. constructor. apply H2. lia. lia.
  * exists e, 0. split; [ auto | split; [ now constructor | lia ] ].
  * exists (EFun [] e0), 0. split; [ constructor | do 2 constructor]. lia.
  * exists e, 0. split; [ auto | split; [now constructor | lia]].
  * exists e, 0. split; [ auto | split; [now constructor | lia] ].
  * apply H in H4 as HH. destruct HH, H1, H1, H2. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    - apply H in H9. 2: lia. destruct H9, H5, H5, H6.
      exists x0, (S (x1 + S x2)). split. auto. split.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor. auto. lia.
    - apply H in H12. 2: lia. destruct H12, H5, H5, H6.
      exists x2, (S (x1 + S x3)). split. auto. split.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor; auto. auto. lia.
  * apply H in H4 as HH. destruct HH, H1, H1, H2. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    apply H in H10 as HH. destruct HH, H5, H5, H6. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H10) in H6 as H6'.
    inversion H6'; subst; try inversion_is_value.
    exists (ELit (n + m)), (S (x1 + (S (x3 + 1)))).
    split. constructor. split.
    econstructor. constructor. eapply transitive_eval; eauto. 
    econstructor. constructor; auto. eapply transitive_eval; eauto.
    econstructor. constructor. constructor. lia.
  * apply H in H4 as v_eval. 2: lia. destruct v_eval, H1, H1, H2.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    destruct vs.
    - inversion H2'; subst; try inversion_is_value.
      apply H in H8. 2: lia. destruct H8, H5, H5, H7.
      exists x0, (S (x1 + S x2)). split; auto. split.
      econstructor. constructor. eapply transitive_eval; eauto.
      econstructor. constructor. auto. lia.
    - inversion H2'; subst; try inversion_is_value.
      epose proof (term_eval_app vs [] x0 k e Fs ltac:(auto) H9 H11 _).
      destruct H5, H5, H5, H6. inversion H6; subst; try inversion_is_value.
      inversion H8; subst; try inversion_is_value.
      inversion H12; subst. apply cons_neq in H16. contradiction.
      inversion H13; subst; try inversion_is_value.
      exists x2, (S (x1 + S k1)). split; auto.
      split.
      econstructor. constructor. eapply transitive_eval; eauto. lia.
    Unshelve.
      intros. apply H with (m := m); eauto. lia.
  * apply H in H4 as HH. destruct HH, H1, H1, H2. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    apply H in H11 as HH. destruct HH, H5, H5, H6. 2: lia.
    eapply (terminates_step_any_2 _ _ _ _ H11) in H6 as H6'.
    exists x2, (S (x1 + (S x3))).
    split. auto. split.
    econstructor. constructor. eapply transitive_eval; eauto. 
    econstructor. constructor; auto. auto. lia.
Qed.

Theorem plus_lit : forall v Fs e x,
  | (FPlus2 v) :: Fs, e | x ↓ -> exists l, v = ELit l.
Proof.
  intros. apply term_eval in H as H'. destruct H', H0, H0.
  eapply terminates_step_any_2 in H1. 2: exact H.
  inversion H1; subst; try inversion_is_value.
  now exists n.
Qed.

Inductive frame_wf : Frame -> Prop :=
| wf_app1 l : frame_wf (FApp1 l)
| wf_app2 v l1 l2 : is_value v -> Forall is_value l2 -> frame_wf (FApp2 v l1 l2)
| wf_let v e : frame_wf (FLet v e)
| wf_plus1 e : frame_wf (FPlus1 e)
| wf_plus2 v : is_value v -> frame_wf (FPlus2 v)
| wf_if e2 e3 : frame_wf (FIf e2 e3)
.

Theorem put_back : forall F e Fs,
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓ /\ frame_wf F.
Proof.
  destruct F; intros; simpl.
  * inversion H. split. exists (S x). constructor. auto. constructor.
  * destruct H. admit.
  * inversion H. split. exists (S x). constructor. auto. constructor.
  * inversion H. split. exists (S x). constructor. auto. constructor.
  * inversion H. apply plus_lit in H0 as H'. destruct H'. subst. split.
    exists (S (S x)). do 2 constructor. constructor. auto. do 2 constructor.
  * inversion H. split. exists (S x). constructor. auto. constructor.
Admitted.

Theorem put_back_rev : forall F e Fs, frame_wf F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  destruct F; intros; simpl.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * admit. (* TODO, provable, technically challenging *)
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. inversion H.
    subst. inversion H5; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
Admitted.

(* Theorem partial_step :
  ⟨ fs :: Fs, 

Theorem partial_eval : forall k e v,
  ⟨ [], e ⟩ -[S k]-> ⟨ [], v ⟩
<->
  forall Fs, ⟨ Fs, e ⟩ -[S k]-> ⟨ Fs, v ⟩.
Proof.
  split; revert e v.
  { intros. dependent induction H.
    * 
  
Qed. *)
