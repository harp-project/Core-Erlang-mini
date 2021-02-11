Require Export ExpSemantics.
Import ListNotations.


Reserved Notation "⟨ fs , e ⟩ ↓" (at level 50).
Inductive terminates : FrameStack -> Exp -> Prop :=

| term_value v : is_value v -> ⟨ [] , v ⟩ ↓ (** CAUTION: empty stach is needed here!!!! *)


| term_if_true fs e1 e2 : ⟨ fs , e1 ⟩ ↓ -> ⟨ (FIf e1 e2)::fs , ELit 0 ⟩ ↓
| term_if_false fs e1 e2 v : is_value v -> v <> ELit 0 -> ⟨ fs , e2 ⟩ ↓ -> ⟨ (FIf e1 e2)::fs , v ⟩ ↓
| term_plus_left e2 v fs (H : is_value v) : ⟨ (FPlus2 v H)::fs , e2 ⟩ ↓ -> ⟨ (FPlus1 e2)::fs, v ⟩ ↓
| term_plus_right n m fs H : ⟨ fs , ELit (n + m) ⟩ ↓ -> ⟨ (FPlus2 (ELit n) H )::fs, ELit m ⟩ ↓
| term_let_subst var v e2 fs : is_value v -> ⟨ fs, varsubst var v e2 ⟩ ↓ -> ⟨(FLet var e2)::fs, v ⟩ ↓
| term_letrec_subst f vl b e fs : ⟨ fs, funsubst f (ERecFun f vl b) e ⟩ ↓ -> ⟨ fs, ELetRec f vl b e ⟩ ↓
| term_app_start v hd tl (H : is_value v) fs : 
  ⟨(FApp2 v H tl [] empty_is_value)::fs, hd⟩ ↓ -> ⟨ (FApp1 (hd::tl))::fs, v ⟩ ↓
| term_app1 fs e :  ⟨fs, e ⟩ ↓ -> ⟨ (FApp1 [])::fs, EFun [] e ⟩ ↓
| term_app1_rec f e fs : ⟨fs, funsubst f (ERecFun f [] e) e ⟩ ↓ -> ⟨ (FApp1 [])::fs, ERecFun f [] e ⟩ ↓
| term_app_step v v' H hd tl vs H2 (H' : is_value v') fs :
  ⟨ (FApp2 v H tl (vs ++ [v']) (step_value vs v' H2 H'))::fs, hd ⟩ ↓ -> ⟨ (FApp2 v H (hd::tl) vs H2)::fs , v' ⟩ ↓
| term_app2 v vl e vs fs H H2 : 
  is_value v -> ⟨fs, varsubst_list vl (vs ++ [v]) e ⟩ ↓ -> ⟨ (FApp2 (EFun vl e) H [] vs H2)::fs, v ⟩ ↓
| term_app2_rec v f vl e vs fs H H2 :
  is_value v -> ⟨fs, funsubst f (ERecFun f vl e) (varsubst_list vl (vs ++ [v]) e) ⟩ ↓ 
-> ⟨ (FApp2 (ERecFun f vl e) H [] vs H2)::fs, v ⟩ ↓


| term_if e e1 e2 fs : ⟨ (FIf e1 e2)::fs, e ⟩ ↓ -> ⟨ fs, EIf e e1 e2 ⟩ ↓
| term_plus e1 e2 fs : ⟨ (FPlus1 e2)::fs, e1 ⟩ ↓ -> ⟨ fs, EPlus e1 e2 ⟩ ↓
| term_app e vs fs : ⟨ (FApp1 vs)::fs, e ⟩ ↓ -> ⟨fs, EApp e vs ⟩ ↓
| term_let v e1 e2 fs : ⟨(FLet v e2)::fs, e1  ⟩ ↓ -> ⟨ fs, ELet v e1 e2 ⟩ ↓

where "⟨ fs , e ⟩ ↓" := (terminates fs e).

Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_rt fs e fs' e') (at level 50).
Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e') (at level 50).

Theorem terminates_correct fs e :
  ⟨ fs , e ⟩ ↓ -> exists v, is_value v /\ ⟨ fs, e ⟩ -->* ⟨ [] , v ⟩.
Proof.
  intro. dependent induction H.
  * exists v. split; auto. constructor. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H2. exists x. split. auto. econstructor. constructor. auto. auto. auto.
  * destruct IHterminates, H1. exists x. split. auto. econstructor. constructor. exact H2.
  * destruct IHterminates, H1. exists x. split. auto. econstructor. constructor. exact H2.
  * destruct IHterminates, H1. exists x. split. auto. econstructor. constructor. auto. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H1. exists x. split. auto. econstructor. constructor. exact H2.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H1. exists x. split. auto. econstructor. constructor. exact H3.
  * destruct IHterminates, H3. exists x. split. auto. econstructor. constructor. auto. auto.
  * destruct IHterminates, H3. exists x. split. auto. econstructor. constructor. auto. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
  * destruct IHterminates, H0. exists x. split. auto. econstructor. constructor. auto.
Qed.

Theorem terminates_sound fs e :
  forall v, ⟨ fs, e ⟩ -->* ⟨ [] , v ⟩ -> is_value v ->  ⟨ fs , e ⟩ ↓.
Proof.
  intros v IH. dependent induction IH; intros.
  * constructor. auto.
  * inversion H; subst; try (econstructor; auto; apply IHIH; auto).
Qed.


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

Fixpoint finite_unfolding (n : nat) (f : FunctionIdentifier) (vl : list Var) (b : Exp) : Exp :=
match n with
| 0 => ERecFun f vl b (* <- according to me *)
(* | 0 => ERecFun f vl (EApp (EFunId f) (map EVar vl))  <- TODO: according to the paper *)
| S n' => EFun vl (funsubst f (finite_unfolding n' f vl b) b)
end.

Lemma finite_unfolding_is_value :
  forall n f vl b,
  is_value (finite_unfolding n f vl b).
Proof.
  destruct n; intros; constructor.
Qed.

(*
Definition sum (n : Z) := ELetRec F1 [XVar] (EIf (EVar XVar) (EVar XVar) (
                                            (EPlus (EVar XVar)
                                            (EApp (EFunId F1) [EPlus (EVar XVar) (ELit (-1))]))))
                        (EApp (EFunId F1) [ELit n])
*)
Compute finite_unfolding 1 F1 [XVar] (EIf (EVar XVar) (EVar XVar) (
                                            (EPlus (EVar XVar)
                                            (EApp (EFunId F1) [EPlus (EVar XVar) (ELit (-1))])))).

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

Definition frame_funsubst (f : FunctionIdentifier) (vl : list Var) (b : Exp) (fr : Frame) : Frame :=
match fr with
 | FApp1 l => FApp1 (map (funsubst f (ERecFun f vl b)) l)
 | FApp2 v p l1 l2 p2 => FApp2 v p (map (funsubst f (ERecFun f vl b)) l1) l2 p2
 | FLet v e2 => FLet v (funsubst f (ERecFun f vl b) e2)
 | FPlus1 e2 => FPlus1 (funsubst f (ERecFun f vl b) e2)
 | FPlus2 v p => FPlus2 v p
 | FIf e2 e3 => FIf (funsubst f (ERecFun f vl b) e2) (funsubst f (ERecFun f vl b) e3)
end.

Definition framestack_funsubst (l : FrameStack) (f : FunctionIdentifier) (vl : list Var) (b : Exp) 
   : FrameStack := map (frame_funsubst f vl b) l.

Lemma unwinding_increase n :
forall fs f vl b e,
  ⟨ framestack_funsubst fs f vl b, funsubst f (finite_unfolding n f vl b) e ⟩ ↓
->
  ⟨ framestack_funsubst fs f vl b, funsubst f (finite_unfolding (S n) f vl b) e ⟩ ↓.
Proof.
  induction n; intros.
  * admit. (* inversion H; simpl in *; subst. admit. *)
  * admit.
Admitted.

Theorem unwinding e f vl b :
  forall fs, ⟨ framestack_funsubst fs f vl b, funsubst f (ERecFun f vl b) e ⟩ ↓
->
  exists n, ⟨ framestack_funsubst fs f vl b, funsubst f (finite_unfolding n f vl b) e ⟩ ↓.
Proof.
  (* intros fs IH. dependent induction IH; subst.
  * destruct e; simpl in *; try ( exists 0; constructor; auto); try inversion H;
    try break_match_goal; try inversion H; subst; rewrite <- x. all: exists 0.
    all: simpl; econstructor; constructor.
  * destruct e; simpl in x; inversion x. 2-3: simpl; break_match_goal; inversion x.
    exists 0. rewrite <- x0. constructor. auto.
  * destruct e; simpl in *; try inversion H; try break_match_goal; try congruence.
    1, 3-4: exists 0; rewrite <- x; econstructor; auto.
    exists 0. rewrite <- x. constructor; auto. (*  apply finite_unfolding_is_value. simpl. congruence. *)
  * destruct e; remember H as H'; clear HeqH'; simpl in H; simpl; try break_match_goal; try inversion H.
    1, 3-4: exists 0; rewrite <- x; simpl in IH; apply term_plus_left with (H := H'); auto.
    subst. rewrite <- x. eexists. econstructor. *)
Admitted.


(* 
Theorem termination_simulation :
  (forall (e1 e2 : Exp) (v1 v2 : Exp),
    ((* forall fs : FrameStack, *) ⟨ [], e1 ⟩ -->* ⟨ [], v1 ⟩) -> is_value v1 ->
    ((* forall fs : FrameStack, *) ⟨ [], e2 ⟩ -->* ⟨ [], v2 ⟩) -> is_value v2 ->
    term_preorder v1 v2 
  ->
    term_preorder e1 e2)
.
Proof.

Admitted. *)

Theorem varsubst_funsubst_comm :
  forall e f e' e'' v, funsubst f e' (varsubst v e'' e) = varsubst v e'' (funsubst f e' e).
Proof.
  induction e; intros; try reflexivity.
  * simpl. break_match_goal.
Abort.

Lemma unwinding_increase_functionaé clock :
forall n v f vl b e,
  eval clock (funsubst f (finite_unfolding n f vl b) e) = Some v
->
  exists clock' v', eval clock' (funsubst f (finite_unfolding (S n) f vl b) e) = Some v'. (** termination *)
Proof.
  induction clock; intros.
  * inversion H.
  * destruct e; simpl in H.
    - exists 1, v. simpl. auto.
    - exists 1, v. simpl. auto.
    - exists 1. simpl. destruct (((fst f0 =? fst f)%string && Nat.eqb (snd f0) (snd f))%bool).
      + eexists. reflexivity.
      + inversion H.
    - exists 1, v. simpl. auto.
    - exists 1, v. simpl. auto.
    - admit.
    - break_match_hyp. 2: congruence. (* apply IHclock in H. *) (** substitution is not commutative!!! *)
    (** Environments are needed *)
Abort.

Inductive Value : Set :=
| VLit (z : Z)
| VFun (env : list ((Var + FunctionIdentifier) * Value)) (vl : list Var) (b : Exp)
| VRecFun (env : list ((Var + FunctionIdentifier) * Value)) (f : FunctionIdentifier) (vl : list Var) (b : Exp).


Definition Environment : Set := list ((Var + FunctionIdentifier) * Value).


(* The equality of function signatures *)
  Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (* Extended equality between functions and vars *)
  Definition var_funid_eqb (v1 v2 : Var + FunctionIdentifier) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.

(** Get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   : option Value :=
match env with
| [ ] => None
| (k,v)::xs => if var_funid_eqb key k then Some v else get_value xs key
end.

(** Insert *)
Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   (value : Value) : Environment :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if var_funid_eqb k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end.

(** Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => []
end.

Inductive ResultType {T : Set} : Set :=
| Timeout
| Fail
| Res (v : T)
.

Fixpoint eval_list (f : Exp -> @ResultType Value) (l : list Exp) : @ResultType (list Value) :=
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

Fixpoint eval_env (clock : nat) (env : Environment) (e : Exp) : @ResultType Value :=
match clock with
| 0 => Timeout
| S n => match e with
         | ELit l => Res (VLit l)
         | EVar v => match get_value env (inl v) with
                     | Some val => Res val
                     | None => Fail
                     end
         | EFunId f => match get_value env (inr f) with
                       | Some val => Res val
                       | None => Fail
                       end
         | EFun vl e => Res (VFun env vl e)
         | ERecFun f vl e => Res (VRecFun env f vl e)
         | EApp exp l => match eval_env n env exp with
                         (** In Core Erlang this check only happens later *)
                         | Res (VFun env' vl e) =>
                            (* This would be better with Monads *)
                            let vres := eval_list (eval_env n env) l in
                               match vres with
                               | Res vals => eval_env n (append_vars_to_env vl vals env') e
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res (VRecFun env' f vl e) =>
                            let vres := eval_list (eval_env n env) l in
                               match vres with
                               | Res vals => eval_env n (append_vars_to_env vl vals (insert_value env' (inr f) (VRecFun env' f vl e))) e
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res _  => Fail
                         | r => r
                         end
         | ELet v e1 e2 => match eval_env n env e1 with
                           | Res val => eval_env n (insert_value env (inl v) val) e2
                           | r      => r
                           end
         | ELetRec f vl b e => eval_env n (insert_value env (inr f) (VRecFun env f vl b)) e
         | EPlus e1 e2 => 
            match eval_env n env e1, eval_env n env e2 with
            | Res (VLit n), Res (VLit m) => Res (VLit (n + m))
            | Res _, Res _ => Fail
            | Res _, r => r
            | r, _     => r
            end
         | EIf e1 e2 e3 =>
            match eval_env n env e1 with
            | Res (VLit 0) => eval_env n env e2
            | Res _        => eval_env n env e3
            | r            => r
            end
        end
end.

Definition make_exp (v : Value) : Exp :=
match v with
 | VLit z => ELit z
 | VFun env vl b => EFun vl b
 | VRecFun env f vl b => ERecFun f vl b
end.

Definition make_exps (l : list Value) : list Exp := map make_exp l.


(* Termination and ctx equivalence *)


(* Definition term_preorder (e1 e2 : Exp) : Prop :=
  forall (C : Context),  ⟨ [], C[[ e1 ]] ⟩ ↓ -> ⟨ [], C [[ e2 ]] ⟩ ↓. *)

Definition terminating (e : Exp) (env : Environment) : Prop :=
  exists v clock, eval_env clock env e = Res v
.

Notation "⟨ env | e ⟩ ↓" := (terminating e env) (at level 50).

Definition term_preorder (e1 e2 : Exp) : Prop :=
  forall (C : Context) env,  ⟨ env | C[[ e1 ]] ⟩ ↓ -> 
                             ⟨ env | C[[ e2 ]] ⟩ ↓.

Definition term_equivalent (e1 e2 : Exp) : Prop :=
  term_preorder e1 e2 /\ term_preorder e2 e1.

Lemma term_preorder_refl :
  forall e, term_preorder e e.
Proof. firstorder. Qed.

Lemma term_preorder_trans :
  forall e1 e2 e3, term_preorder e1 e2 -> term_preorder e2 e3
->
  term_preorder e1 e3.
Proof.
  unfold term_preorder; intros.
  apply H in H1. apply H0 in H1. exact H1.
Qed.

Lemma term_eq_refl :
  forall e, term_equivalent e e.
Proof. firstorder. Qed.

Lemma term_eq_sym :
  forall e1 e2, term_equivalent e1 e2 -> term_equivalent e2 e1.
Proof. firstorder. Qed.

Lemma term_eq_trans :
  forall e1 e2 e3,
  term_equivalent e1 e2 -> term_equivalent e2 e3
->
  term_equivalent e1 e3.
Proof. 
  unfold term_equivalent. intros.
  destruct H, H0. split.
  eapply term_preorder_trans. exact H. auto.
  eapply term_preorder_trans. exact H2. auto.
Qed.

(* local to ctx *)

Axiom bigger_clock :
  forall env e clock v clock', clock' >= clock ->
   eval_env clock env e = Res v ->
   eval_env clock' env e = Res v.

Goal forall e1 e2,
  (forall env, ⟨ env | e1 ⟩ ↓ -> ⟨ env | e2 ⟩ ↓)
->
  term_preorder e1 e2.
Proof.
  (* intros. unfold term_preorder. intro. dependent induction C; intros; simpl fill_boxes in *; auto.
  * unfold terminating. eexists. exists 1. reflexivity.
  * unfold terminating. eexists. exists 1. reflexivity.
  * admit.
  * unfold terminating in *. destruct H0, H0.
    destruct x0. inversion H0. simpl in H0. break_match_hyp. 2: congruence.
    apply ex_intro with (x := x0) in Heqo as Heqo'. apply ex_intro with (x := v0) in Heqo'.
    apply IHC1 in Heqo'.
    apply ex_intro with (x := x0) in H0. apply ex_intro with (x := x) in H0. apply IHC2 in H0.
    destruct Heqo', H0, H0, H1. exists x2, (S (x3 + x4)). simpl.
    eapply bigger_clock in H1. rewrite H1. eapply bigger_clock in H0.
    apply bigger_clock with (clock' := x3 + x4) in Heqo. *) (** Wrong <- termination is not strong enough **)
Abort.

(** counterexample: ELit 0 ~ ELit 1 in C := EIf □ (ELit 0) (EVar X) *)


Inductive preorder_vals : Value -> Value -> Prop :=
| refl v : preorder_vals v v
| funclos env vl b env' vl' b':
  (forall exps, preorder_exps_env env (EApp (EFun vl b) exps) env' (EApp (EFun vl' b') exps) )
->
  preorder_vals (VFun env vl b) (VFun env' vl' b')
with preorder_exps_env : Environment -> Exp -> Environment -> Exp -> Prop :=
| equiv_exp e1 env1 e2 env2 v1 v2 :
  preorder_vals v1 v2 ->
  ((exists clock, eval_env clock env1 e1 = Res v1) ->
  (exists clock, eval_env clock env2 e2 = Res v2))
->
  preorder_exps_env env1 e1 env2 e2
.


Scheme ind1 := Induction for preorder_vals Sort Prop
with ind2 := Induction for preorder_exps_env Sort Prop.
Check ind2.

Combined Scheme equiv_strict_ind from ind1, ind2.

Definition exp_preorder e1 e2 : Prop :=
  forall env, preorder_exps_env env e1 env e2.

Goal exp_preorder (ELit 0) (ELit 1).
Proof.
  econstructor. instantiate (1 := VLit 5). instantiate (1 := VLit 5). constructor.
  intros. destruct H, x; inversion H.
Qed.

Lemma preorder_vals_refl :
  forall v, preorder_vals v v.
Proof. constructor. Qed.


Lemma exp_preorder_refl :
  forall e, exp_preorder e e.
Proof.
  intros. unfold exp_preorder. intros. econstructor.
  2: { intros. exact H. } constructor. Unshelve. exact (VLit 0).
Qed. 








(* TODO NOT strictly positive :(

Inductive equiv_rel_exp : Exp -> Exp -> Prop :=
| exp_equiv e1 e2 env v1 v2: 
  (exists clock, eval_env clock env e1 = Some v1) ->
  (exists clock, eval_env clock env e2 = Some v2) ->
   equiv_rel_val v1 v2
->
  equiv_rel_exp e1 e2
with equiv_rel_val : Value -> Value -> Prop :=
| lit_equiv l : equiv_rel_val (VLit l) (VLit l)
| fun_equiv vl vl' e e' env env' : 
  forall exps1 exps2, length exps1 = length exps2 ->
  (forall i, i < length exps1 -> equiv_rel_exp (nth i exps1 (ELit 0)) (nth i exps2 (ELit 0))) ->
  equiv_rel_exp (EApp (EFun vl e) exps1) (EApp (EFun vl' e') exps2)
->
  equiv_rel_val (VFun env vl e) (VFun env' vl' e')
| recfun_equiv vl vl' e e' env env' f f' : 
  (forall (exps1 exps2 : list Value), length exps1 = length exps2 ->
  (forall i, i < length exps1 -> equiv_rel_val (nth i exps1 (VLit 0)) (nth i exps2 (VLit 0))) ->
  equiv_rel_exp (EApp (ERecFun f vl e) (make_exps exps1)) (EApp (ERecFun f' vl' e') (make_exps exps2)))
->
  equiv_rel_val (VRecFun env f vl e) (VRecFun env' f' vl' e')
. *)

(* Fixpoint value_equiv (v1 v2 : Value) : Prop :=
match v1, v2 with
| VLit l1, VLit l2 => True
| VFun env vl b, VFun env' vl' b' =>
  forall 
| _, _ => False
end.


Definition equivalent (e1 e2 : Exp) : Prop :=
  forall v1 v2,
    value_equiv v1 v2 ->
    (exists clock, eval_env clock env e1 = Some v1 ->
                   eval_env clock env e2 = Some v2). *)



(* Inductive trial : Exp -> Exp -> Prop:=
| exp_equiv e1 e2 :

with trial_val : Value -> Value -> Prop :=
| refl_equiv v : trial_val v v
| funn env env' vl vl' e e' : 
  
->
  trial_val (VFun env vl e) (VFun env' vl' e')
. *)

Unset Positivity Checking.

Module wrong_rel.
 
 Inductive val_rel : Value -> Value -> Prop :=
(* | lit_rel z z' : 
  z = z' -> val_rel (VLit z) (VLit z') *)
| refl_rel v : val_rel v v
| clos_rel vl env b vl' env' b' :
  (forall vals,
  exp_rel (append_vars_to_env vl vals env) (append_vars_to_env vl' vals env') b b')
->
  val_rel (VFun env vl b) (VFun env' vl' b')
with exp_rel : Environment -> Environment -> Exp -> Exp -> Prop :=
(* | exp_rel_cons env env' e1 e2: (* not transitive! *)
  (forall v1 v2 clock,
      eval_env clock env e1 = Res v1 /\
      eval_env clock env' e2 = Res v2 ->
      val_rel v1 v2)
->
  exp_rel env env' e1 e2 *)
 | exp_rel_cons env env' e1 e2:
  (forall clock,
      match eval_env clock env e1, eval_env clock env' e2 with
      | Res v1, Res v2 => val_rel v1 v2
      | _, _ => True
      end)
->
  exp_rel env env' e1 e2
(* | exp_rel_cons env env' e1 e2:
  (forall v1 v2 clock,
    val_rel v1 v2 ->
     eval_env clock env e1 = Res v1 <-> (* exists clock needed, cannot be used to reason about divergent programs *)
     eval_env clock env' e2 = Res v2)
->
  exp_rel env env' e1 e2 *)
.

Definition inf f := EApp (ERecFun f [] (EApp (EFunId f) [])) [].

Axiom alma : forall f clock env, eval_env clock env (inf f) = Timeout.

Goal forall f env, exp_rel env env (ELit 0) (inf f). (* Non-termination is equivalent to termination *)
Proof.
  intros. constructor. intros.
  destruct clock.
  * simpl. auto.
  * rewrite alma. break_match_goal; auto.
Qed.

End wrong_rel.

Inductive val_rel : Value -> Value -> Prop :=
(* | lit_rel z z' : 
  z = z' -> val_rel (VLit z) (VLit z') *)
| refl_rel v : val_rel v v
| clos_rel vl env b vl' env' b' :
  (forall vals,
  exp_rel (append_vars_to_env vl vals env) (append_vars_to_env vl' vals env') b b')
->
  val_rel (VFun env vl b) (VFun env' vl' b')
with exp_rel : Environment -> Environment -> Exp -> Exp -> Prop :=
| exp_rel_cons env env' e1 e2: (* not transitive! *)
  (terminating e1 env <-> terminating e2 env') ->
  (forall v1 v2 clock,
      eval_env clock env e1 = Res v1 /\
      eval_env clock env' e2 = Res v2 ->
      val_rel v1 v2)
->
  exp_rel env env' e1 e2
(* TODO: recursion *)
(* | exp_rel_cons env env' e1 e2:
  (forall clock,
      match eval_env clock env e1, eval_env clock env' e2 with
      | Res v1, Res v2 => val_rel v1 v2
      | _, _ => True
      end)
->
  exp_rel env env' e1 e2 *)
(* | exp_rel_cons env env' e1 e2:
  (forall v1 v2 clock,
    val_rel v1 v2 ->
     eval_env clock env e1 = Res v1 <-> (* exists clock needed, cannot be used to reason about divergent programs *)
     eval_env clock env' e2 = Res v2)
->
  exp_rel env env' e1 e2 *)
.

(* Inductive exp_rel : Exp -> Exp -> Prop :=
(* | lit_rel z z' : 
  z = z' -> val_rel (VLit z) (VLit z') *)
| refl_rel v : is_value v -> exp_rel v v
| clos_rel vl env b vl' env' b' :
  (forall vals,
    (forall v1 v2 clock, eval_env clock (append_vars_to_env vl vals env) b = Res v1 /\
                   eval_env clock (append_vars_to_env vl' vals env') b' = Res v2 ->
    exp_rel (make_exp v1) (make_exp v2))
  (* exp_rel (append_vars_to_env vl vals env) (append_vars_to_env vl' vals env') b b' *))
->
  exp_rel (make_exp (VFun env vl b)) (make_exp (VFun env' vl' b'))
| exp_rel_cons e1 e2:
  (forall env v1 v2 clock,
      eval_env clock env e1 = Res v1 /\
      eval_env clock env e2 = Res v2 ->
      exp_rel (make_exp v1) (make_exp v2))
->
  exp_rel e1 e2
.

Scheme exp_rel_ind := Induction for exp_rel Sort Prop.
Check exp_rel_ind. *)

Set Positivity Checking.

Scheme ind11 := Induction for val_rel Sort Prop
with ind22 := Induction for exp_rel Sort Prop.

Check ind22.

Combined Scheme exp_rel_ind from ind11, ind22.

Check exp_rel_ind.

Goal forall x (P : Value -> Prop),
  match x with
  | Res y => P y
  | _     => True
  end
  <->
  (forall y, x = Res y -> P y).
Proof.
  split; intros.
  destruct x; inversion H0. subst. auto.
  destruct x; auto.
Qed.

Goal forall x y (P : Value -> Value -> Prop),
  match x, y with
  | Res x', Res y' => P x' y'
  | _ , _          => True
  end
  <->
  (forall x' y', x = Res x' /\ y = Res y' -> P x' y').
Proof.
  split; intros.
  * destruct H0. subst. auto.
  * destruct x, y; auto.
Qed.

Definition equiv_rel e1 e2 : Prop :=
  forall env, exp_rel env env e1 e2
.

Theorem val_rel_refl :
  forall v, val_rel v v.
Proof.
  constructor.
Qed.

Theorem exp_rel_refl :
  forall env e, exp_rel env env e e.
Proof.
  intros. constructor.
  * split; auto.
  * intros. destruct H. rewrite H in H0. inversion H0. constructor.
Qed.

Theorem equiv_rel_refl :
  forall e, equiv_rel e e.
Proof.
  econstructor. intros.
  * split; auto.
  * intros. destruct H. rewrite H in H0. inversion H0. constructor.
Qed.

Check exp_rel_ind.

Theorem val_rel_sym :
  (forall v1 v2, val_rel v1 v2 -> val_rel v2 v1)
/\
  (forall env env' v1 v2, exp_rel env env' v1 v2 -> exp_rel env' env v2 v1).
Proof.
  intros. apply exp_rel_ind.
  * constructor.
  * constructor. intros. apply H.
  * intros. constructor.
    - destruct i. split; auto.
    - intros. eapply H. destruct H0. split. exact e0. exact e.
Qed. 

Theorem equiv_rel_sym:
  forall e1 e2, equiv_rel e1 e2 -> equiv_rel e2 e1.
Proof.
  unfold equiv_rel in *. intros. apply val_rel_sym. apply H.
Qed.

Theorem val_rel_trans :
  (forall v1 v2, val_rel v1 v2 -> (forall v3, val_rel v2 v3 -> val_rel v1 v3))
/\
  (forall env1 env2 e1 e2, exp_rel env1 env2 e1 e2 -> (forall env3 e3, exp_rel env2 env3 e2 e3 -> exp_rel env1 env3 e1 e3)).
Proof.
  apply exp_rel_ind; intros.
  * auto.
  * inversion H0.
    - subst. constructor. intros. apply H. apply exp_rel_refl.
    - subst. constructor. intros. apply H. apply H5.
  * inversion H0. subst. constructor.
    - eapply iff_trans. exact i. auto.
    - intros. destruct H3.
      apply ex_intro with (x := clock) in H3 as Hex. apply ex_intro with (x := v1) in Hex.
      apply ex_intro with (x := clock) in H4 as H0ex. apply ex_intro with (x := v2) in H0ex.
      apply i in Hex. apply H1 in H0ex. destruct Hex, H0ex, H5, H6.
      apply bigger_clock with (clock' := clock + x1) in H3.
      apply bigger_clock with (clock' := clock + x1) in H5.
      apply bigger_clock with (clock' := clock + x1) in H4. all: try lia.
      pose (H v1 x _ (conj H3 H5)). apply v0.
      
      destruct H0.
      epose (H7 _ _ _ (conj H5 _)). exact v3. Unshelve. auto.
Qed.

Theorem equiv_rel_trans :
  forall e1 e2 e3, equiv_rel e1 e2 -> equiv_rel e2 e3 -> equiv_rel e1 e3.
Proof.
  unfold equiv_rel. intros. eapply val_rel_trans. apply H. apply H0.
Qed.


(** TODO: I don't think this is strong enough  *)
Inductive equiv_rel_exp_strict : Exp -> Exp -> Prop :=
(* | exp_equiv0 e1 e2: 
  (forall env v1 v2, 
    (exists clock, 
      eval_env clock env e1 = Some v1 /\
      eval_env clock env e2 = Some v2) /\
     equiv_rel_val_strict v1 v2)
->
  equiv_rel_exp_strict e1 e2 *)
| exp_equiv0 e1 e2 (* v1 v2 (p : equiv_rel_val_strict v1 v2) <- This is wrong *) : 
  (forall env,
    (exists clock v1, eval_env clock env e1 = Some v1) <->
    (exists clock v2, eval_env clock env e2 = Some v2) /\
    (forall v1 v2,
      (exists clock, eval_env clock env e2 = Some v1) /\
      (exists clock, eval_env clock env e2 = Some v2) ->
      equiv_rel_val_strict v1 v2)
  )
->
  equiv_rel_exp_strict e1 e2
with equiv_rel_val_strict : Value -> Value -> Prop :=
| refl_equiv0 v : equiv_rel_val_strict v v
| fun_equiv0 vl vl' e e' env env' : 
  forall exps,
  (* (forall exps1 exps2, length exps1 = length exps2 ->
  (forall i, i < length exps1 -> equiv_rel_val_strict (nth i exps1 (VLit 0)) (nth i exps2 (VLit 0))) *)
  equiv_rel_exp_strict (EApp (EFun vl e) (make_exps exps)) (EApp (EFun vl' e') (make_exps exps))
->
  equiv_rel_val_strict (VFun env vl e) (VFun env' vl' e')
(* | recfun_equiv0 vl vl' e e' env env' f f' : 
  (forall (exps1 exps2 : list Value), length exps1 = length exps2 ->
  (forall i, i < length exps1 -> equiv_rel_val_strict (nth i exps1 (VLit 0)) (nth i exps2 (VLit 0))) ->
  equiv_rel_exp_strict (EApp (ERecFun f vl e) (make_exps exps1)) (EApp (ERecFun f' vl' e') (make_exps exps2)))
->
  equiv_rel_val_strict (VRecFun env f vl e) (VRecFun env' f' vl' e') *)
.

Goal equiv_rel_exp_strict (ELit 0) (EVar "X"%string).
Proof.
  constructor. intros. destruct H, H0. destruct x0. inversion H0. inversion H0.
  

Scheme ind1 := Induction for equiv_rel_exp_strict Sort Prop
with ind2 := Induction for equiv_rel_val_strict Sort Prop.
Combined Scheme equiv_strict_ind from ind1, ind2.

Check equiv_strict_ind.

Theorem equiv_rel_val_refl :
  (forall e, equiv_rel_val_strict e e).
Proof.
  intros. constructor.
Qed.

Axiom alma : forall env env' e e' v1 v2,
  (exists clock : nat, eval_env clock env e = Some v1) ->
  (exists clock' : nat, eval_env clock' env' e' = Some v2) ->
  exists clock : nat, eval_env clock env e = Some v1 /\ eval_env clock env' e' = Some v2.


Theorem equiv_rel_exp_refl :
  (forall e, equiv_rel_exp_strict e e).
Proof.
  intros. constructor. intros. pose(alma _ _ _ _ _ _ H H0). destruct e0, H1.
  rewrite H1 in H2. inversion H2. subst.
  apply equiv_rel_val_refl.
Qed.

Theorem equiv_rel_exp_sym :
  (forall e1 e2, equiv_rel_exp_strict e1 e2 -> equiv_rel_exp_strict e2 e1) /\
  (forall e1 e2, equiv_rel_val_strict e1 e2 -> equiv_rel_val_strict e2 e1).
Proof.
  apply equiv_strict_ind.
  * intros. constructor. intros.
    eapply H in H1. exact H1. auto.
  * firstorder. constructor.
  * intros. econstructor. exact H.
  (* * intros. constructor. exact H. *)
Qed.

Check equiv_strict_ind.

Theorem equiv_rel_exp_trans :
  (forall e1 e2, equiv_rel_exp_strict e1 e2 -> (forall e3, equiv_rel_exp_strict e2 e3 -> equiv_rel_exp_strict e1 e3))
 /\
  (forall e1 e2, equiv_rel_val_strict e1 e2 -> (forall e3, equiv_rel_val_strict e2 e3 -> equiv_rel_val_strict e1 e3)).
Proof.
  apply equiv_strict_ind; intros.
  * constructor 1. intros env v1 v3 HH HHH. destruct H0. eapply H0. (** warning!! /\ is needed *)
Admitted.












Inductive equiv_rel_exp : Exp -> Exp -> Prop :=
| exp_equiv e1 e2: 
  ~ is_value e1 -> ~ is_value e2 ->
  (forall env v1 v2, 
    (exists clock, eval_env clock env e1 = Some v1 /\
     eval_env clock env e2 = Some v2) /\
     equiv_rel_exp (make_exp v1) (make_exp v2))
->
  equiv_rel_exp e1 e2
| refl_equiv l : is_value l -> equiv_rel_exp l l
| fun_equiv vl vl' e e' : 
  (forall exps,
  equiv_rel_exp (EApp (EFun vl e) exps) (EApp (EFun vl' e') exps))
->
  equiv_rel_exp (EFun vl e) (EFun vl' e')
| recfun_equiv vl vl' e e' f f' : 
  (forall exps,
  equiv_rel_exp (EApp (ERecFun f vl e) exps) (EApp (ERecFun f' vl' e') exps))
->
  equiv_rel_exp (ERecFun f vl e) (ERecFun f' vl' e')
.

Check equiv_rel_exp_ind.

Axiom equiv_rel_exp_ind_correct :
 forall P : Exp -> Exp -> Prop,
       (forall e1 e2 : Exp,
        ~ is_value e1 ->
        ~ is_value e2 ->
        (forall (env : Environment) (v1 v2 : Value),
         (exists clock : nat, eval_env clock env e1 = Some v1 /\ eval_env clock env e2 = Some v2) /\
         equiv_rel_exp (make_exp v1) (make_exp v2) 
         (* ADDITION *)
         /\ P (make_exp v1) (make_exp v2) 
         (***)
         ) -> P e1 e2) ->
       (forall l : Exp, is_value l -> P l l) ->
       (forall (vl vl' : list Var) (e e' : Exp),
        (forall exps : list Exp, equiv_rel_exp (EApp (EFun vl e) exps) (EApp (EFun vl' e') exps)) ->
        (forall exps : list Exp, P (EApp (EFun vl e) exps) (EApp (EFun vl' e') exps)) ->
        P (EFun vl e) (EFun vl' e')) ->
       (forall (vl vl' : list Var) (e e' : Exp) (f2 f' : FunctionIdentifier),
        (forall exps : list Exp,
         equiv_rel_exp (EApp (ERecFun f2 vl e) exps) (EApp (ERecFun f' vl' e') exps)) ->
        (forall exps : list Exp, P (EApp (ERecFun f2 vl e) exps) (EApp (ERecFun f' vl' e') exps)) ->
        P (ERecFun f2 vl e) (ERecFun f' vl' e')) -> forall e e0 : Exp, equiv_rel_exp e e0 -> P e e0.

(* Goal
 (forall (e1 e2 : Exp) (v1 v2 : Value) env, 
    (exists clock, eval_env clock env e1 = Some v1) ->
    (exists clock, eval_env clock env e2 = Some v2) ->
    equiv_rel_val_strict v1 v2 
  ->
    equiv_rel_exp_strict e1 e2)
.
Proof.
  intros. econstructor.
  * intros. apply H.
  * apply H0.
  * apply H1.
Qed. *)

Theorem equiv_rel_exp_refl1 :
  forall e, equiv_rel_exp e e.
Proof.
  intros. destruct e.
  1,4-5: constructor 2. all: try constructor.
Admitted.

Theorem equiv_rel_exp_sym1 :
  forall e1 e2, equiv_rel_exp e1 e2 -> equiv_rel_exp e2 e1.
Proof.
  firstorder.
  induction H; subst.
  * constructor; auto. intros.
    assert (exists clock : nat, eval_env clock env e1 = Some v2 /\ eval_env clock env e2 = Some v1).
    { destruct H3, H3. exists x. split; auto. } eapply H2. exact H4.
  * constructor 2.
  * constructor 3. exact H0.
  * constructor 4. exact H0.
Qed.

(*
Definition ctx_preorder (e1 e2 : Exp) : Prop :=
  forall env v1 v2,
  (exists clock, eval_env clock env e1 = Some v1 /\
  eval_env clock env e2 = Some v2)
->
  equiv_rel_val_strict v1 v2
.

Definition ctx_equivalent (e1 e2 : Exp) : Prop :=
  ctx_preorder e1 e2 /\ ctx_preorder e2 e1
.

Lemma ctx_preorder_refl :
  forall e, ctx_preorder e e.
Proof.
  unfold ctx_preorder. intros. destruct H, H. rewrite H in H0. inversion H0.
  subst. destruct v2; try constructor.
  * econstructor. intros.
Qed.

Lemma ctx_preorder_trans :
  forall e1 e2 e3, ctx_preorder e1 e2 -> ctx_preorder e2 e3
->
  ctx_preorder e1 e3.
Proof. firstorder. Qed.

Lemma ctx_eq_refl :
  forall e, ctx_equivalent e e.
Proof. firstorder. Qed.

Lemma ctx_eq_sym :
  forall e1 e2, ctx_equivalent e1 e2 -> ctx_equivalent e2 e1.
Proof. firstorder. Qed.

Lemma ctx_eq_trans :
  forall e1 e2 e3,
  ctx_equivalent e1 e2 -> ctx_equivalent e2 e3
->
  ctx_equivalent e1 e3.
Proof. firstorder. Qed.

Theorem contextual_equiv :


Theorem uwinding_functional clock : forall f vl b e v env,
  (eval_env clock env (funsubst f (ERecFun f vl b) e) = Some v)
->
  exists n clock', eval_env clock' env (funsubst f (finite_unfolding n f vl b) e) = Some v.
Proof.
  induction clock; intros.
  * inversion H.
  * destruct e; simpl in H; subst.
    - inversion H. simpl. exists 1, 1. auto.
    - inversion H.
    - destruct (((fst f0 =? fst f)%string && Nat.eqb (snd f0) (snd f))%bool) eqn:P; inversion H.
      + simpl. rewrite P. exists 0, 1. simpl. auto.
    - inversion H. subst. exists 1, 1. simpl. auto.
    - simpl. exists 1, 1. simpl. auto.
    - break_match_hyp. apply IHclock in Heqo. destruct Heqo, H0.
      destruct e0; try inversion H.
      + break_match_hyp.


*)




