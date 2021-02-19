Require Export ExpSemantics.
Export PeanoNat.
Export Relations.Relations.
Export Classes.RelationClasses.
Require Export FSets.FMapFacts.

Import ListNotations.

Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_rt fs e fs' e') (at level 50).
Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e') (at level 50).

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

Inductive Value : Set :=
| VLit (z : Z)
(* TODO: strictly positiveness check for maps fail :( *)
| VFun (env : list (VarFunId * Value)) (vl : list Var) (b : Exp)
| VRecFun (env : list (VarFunId * Value)) (f : FunctionIdentifier) (vl : list Var) (b : Exp).

Definition Env : Type := Environment.t Value.


(* The equality of function signatures *)
  Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => String.eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (* Extended equality between functions and vars *)
  Definition var_funid_eqb (v1 v2 : VarFunId) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => String.eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.

  (* (** Get *)
  Fixpoint get_value (env : Environment) (key : VarFunId) 
     : option Value :=
  match env with
  | [ ] => None
  | (k,v)::xs => if var_funid_eqb key k then Some v else get_value xs key
  end. *)

(* (** Insert *)
Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   (value : Value) : Environment :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if var_funid_eqb k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end. *)

(** Add bindings with two lists *)
Definition append_vars_to_env (vl : list Var) (el : list Value) (d : Env)
   : Env :=
fold_right (fun '(key, val) Acc => Environment.add (inl key) val Acc) d (combine vl el)
(* match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => d (** length check needed *)
end *).

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

Compute Environment.elements (Environment.add (inl "a"%string) 1 (Environment.empty _)).

Definition make_env (l : list (VarFunId * Value)) : Env :=
  fold_right (fun '(key, val) Acc => Environment.add key val Acc) (Environment.empty _) l.

Fixpoint eval_env (clock : nat) (env : Env) (e : Exp) : @ResultType Value :=
match clock with
| 0 => Timeout
| S n => match e with
         | ELit l => Res (VLit l)
         | EVar v => match Environment.find (inl v) env with
                     | Some val => Res val
                     | None => Fail
                     end
         | EFunId f => match Environment.find (inr f) env with
                       | Some val => Res val
                       | None => Fail
                       end
         | EFun vl e => Res (VFun (Environment.elements env) vl e)
         | ERecFun f vl e => Res (VRecFun (Environment.elements env) f vl e)
         | EApp exp l => match eval_env n env exp with
                         (** In Core Erlang this check only happens later *)
                         | Res (VFun env' vl e) =>
                            (* This would be better with Monads *)
                            let vres := eval_list (eval_env n env) l in
                               match vres with
                               | Res vals => eval_env n (append_vars_to_env vl vals (make_env env')) e
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res (VRecFun env' f vl e) =>
                            let vres := eval_list (eval_env n env) l in
                               match vres with
                               | Res vals => eval_env n (append_vars_to_env vl vals (Environment.add (inr f) (VRecFun env' f vl e) (make_env env'))) e
                               | Fail => Fail
                               | Timeout => Timeout
                               end
                         | Res _  => Fail
                         | r => r
                         end
         | ELet v e1 e2 => match eval_env n env e1 with
                           | Res val => eval_env n (Environment.add (inl v) val env) e2
                           | r      => r
                           end
         | ELetRec f vl b e => eval_env n (Environment.add (inr f) (VRecFun (Environment.elements env) f vl b) env) e
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

Fixpoint finite_unfolding (n : nat) (f : FunctionIdentifier) (env : Env) (vl : list Var) (b : Exp) : Value :=
match n with
(* | 0 => VRecFun env f vl b (* <- according to me *) *)
| 0 => VRecFun (Environment.elements env) f vl (EApp (EFunId f) (map EVar vl))
| S n' => VFun (Environment.elements (Environment.add (inr f) (finite_unfolding n' f env vl b) env)) vl b
end.

Theorem unwinding clock :
  forall env env' f e vl b val,
  eval_env clock (Environment.add (inr f) (VRecFun (Environment.elements env') f vl b) env) e = Res val
<->
  exists n clock, eval_env clock (Environment.add (inr f) (finite_unfolding n f env' vl b) env) e = Res val
.
Proof.
  split. 
  {
    induction clock; intros.
    * inversion H.
    * admit.
  }
  {
    admit.
  }
Admitted.

Definition make_exp (v : Value) : Exp :=
match v with
 | VLit z => ELit z
 | VFun env vl b => EFun vl b
 | VRecFun env f vl b => ERecFun f vl b
end.

Definition make_exps (l : list Value) : list Exp := map make_exp l.

Definition terminating (e : Exp) (env : Env) : Prop :=
  exists v clock, eval_env clock env e = Res v
.

Axiom bigger_clock :
  forall env e clock v clock', clock' >= clock ->
   eval_env clock env e = Res v ->
   eval_env clock' env e = Res v.

(* TODO: fix this with typing *)
(* Unset Positivity Checking. *)

Inductive val_rel : relation Value :=
(* | lit_rel z z' : 
  z = z' -> val_rel (VLit z) (VLit z') *)
| refl_rel v : val_rel v v
| clos_rel vl env b vl' env' b' :
  length vl = length vl' ->
  (forall vals, length vals = length vl -> (*1 vals2, list_rel vals1 vals2 (* length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> val_rel (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0)) )*) ->*)
  exp_rel (append_vars_to_env vl vals (make_env env)) (append_vars_to_env vl' vals (make_env env')) b b')
->
  val_rel (VFun env vl b) (VFun env' vl' b')
| rec_clos_rel f vl env b f' vl' env' b' :
  length vl = length vl' ->
  (forall vals, length vals = length vl -> (*1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> val_rel (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0))) ->*)
  exp_rel (append_vars_to_env vl vals (Environment.add (inr f) (VRecFun env f vl b) (make_env env))) 
          (append_vars_to_env vl' vals (Environment.add (inr f') (VRecFun env' f' vl' b') (make_env env))) b b')
->
  val_rel (VRecFun env f vl b) (VRecFun env' f' vl' b')
with exp_rel : Env -> Env -> Exp -> Exp -> Prop :=
| exp_rel_cons env env' e1 e2:
  (terminating e1 env <-> terminating e2 env') ->
  (forall v1 v2 clock,
      eval_env clock env e1 = Res v1 /\
      eval_env clock env' e2 = Res v2 ->
      val_rel v1 v2)
->
  exp_rel env env' e1 e2
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
(* with list_rel : list Value -> list Value -> Prop :=
| nil_rel : list_rel [] []
| cons_rel x y xs ys : val_rel x y -> list_rel ys ys -> list_rel (x::xs) (y::ys) *)
.

Scheme ind11 := Induction for val_rel Sort Prop
with ind22 := Induction for exp_rel Sort Prop
(* with ind33 := Induction for list_rel Sort Prop *).

Check ind22.

Combined Scheme exp_rel_ind2 from ind11, ind22(* , ind33 *).

Check exp_rel_ind2.

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

(* Definition equiv_env : relation Env :=
 fun env env' =>
  length env = length env' /\
  forall i, i < length env -> val_rel (snd (nth i env (inl "X"%string, VLit 0))) (snd (nth i env' (inl "X"%string, VLit 0))).

Definition equiv_rel : relation Exp := fun e1 e2 =>
  forall env env', equiv_env env env' -> exp_rel env env' e1 e2
.

Theorem val_rel_refl :
  Reflexive val_rel.
Proof.
  constructor.
Qed.

Theorem exp_rel_refl :
  forall env, Reflexive (exp_rel env env).
Proof.
  intros. constructor.
  * split; auto.
  * intros. destruct H. rewrite H in H0. inversion H0. constructor.
Qed.

Theorem equiv_env_eval :
  forall clock e env env' v, equiv_env env env'
->
  eval_env clock env e = Res v
->
  exists v', eval_env clock env' e = Res v' /\ val_rel v v'.
Proof.
  induction clock; intros.
  * inversion H0.
  * destruct e.
    - simpl in H0. inversion H0.
Admitted.

Corollary equiv_env_term :
  forall env env' e, equiv_env env env' -> terminating e env -> terminating e env'.
Proof.
  intros. unfold terminating in *. destruct H0, H0. eapply equiv_env_eval in H0. 2: exact H. destruct H0, H0.
  eexists. exists x0. exact H0.
Qed.

Theorem val_rel_sym :
  (forall v1 v2, val_rel v1 v2 -> val_rel v2 v1)
/\
  (forall env env' v1 v2, exp_rel env env' v1 v2 -> exp_rel env' env v2 v1)
(* /\
  (forall l1 l2, list_rel l1 l2 -> list_rel l2 l1) *).
Proof.
  intros. apply exp_rel_ind2.
  * constructor.
  * constructor. symmetry. auto. intros. apply H. lia.
  * constructor. symmetry. auto. intros. apply H. lia.
  * intros. constructor.
    - destruct i. split; auto.
    - intros. eapply H. destruct H0. split. exact e0. exact e.
Qed. 

Theorem equiv_env_refl :
  forall env, equiv_env env env.
Proof. firstorder. constructor. Qed.

Theorem equiv_env_sym :
  forall env env', equiv_env env env' -> equiv_env env' env.
Proof.
  firstorder. apply val_rel_sym. apply H0. lia.
Qed.

Theorem equiv_rel_refl :
  forall e, equiv_rel e e.
Proof.
  econstructor. intros.
  * split; apply equiv_env_term; auto. apply equiv_env_sym. auto.
  * intros. destruct H0. epose (equiv_env_eval _ _ _ _ _ H H0). destruct e0, H2. rewrite H1 in H2.
    inversion H2. subst. auto.
Qed.

Check exp_rel_ind.

Theorem equiv_rel_sym:
  forall e1 e2, equiv_rel e1 e2 -> equiv_rel e2 e1.
Proof.
  unfold equiv_rel in *. intros. apply val_rel_sym. eapply H. apply equiv_env_sym. auto.
Qed.

Theorem val_rel_trans :
  (forall v1 v2, val_rel v1 v2 -> (forall v3, val_rel v2 v3 -> val_rel v1 v3))
/\
  (forall env1 env2 e1 e2, exp_rel env1 env2 e1 e2 -> (forall env3 e3, exp_rel env2 env3 e2 e3 -> exp_rel env1 env3 e1 e3)).
Proof.
  apply exp_rel_ind2; intros.
  * auto.
  * inversion H0.
    - subst. constructor. lia. intros. apply H. lia. apply exp_rel_refl.
    - subst. constructor. lia. intros. apply H. lia. apply H6. lia.
  * inversion H0.
    - subst. constructor. lia. intros. apply H. lia. apply exp_rel_refl.
    - subst. constructor. lia. intros. apply H. lia. apply H7. lia.
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
  unfold equiv_rel. intros. eapply val_rel_trans. eapply H. exact H1. (* I can choose equiv_env for e2 *)
  eapply H0. apply equiv_env_refl.
Qed. *)

(* Tactic Notation "start_equiv" := unfold equiv_rel; intros; constructor.
Tactic Notation "prove_term" := split; intros; eexists; exists 1000; simpl; reflexivity. *)

(* Goal
  equiv_rel (ELit 5) (EPlus (ELit 5) (ELit 0)).
Proof.
  start_equiv. prove_term.
  * intros. destruct H0. destruct clock; inversion H0.
    destruct clock; inversion H1. constructor.
Qed.

Goal
  equiv_rel (EFun [] (ELit 1)) (EFun [] (EPlus (ELit 0) (ELit 1))).
Proof.
  start_equiv. prove_term.
  intros. destruct H0. destruct clock; inversion H0. inversion H1. subst.
  constructor. intros. auto. simpl.
  intros. apply length_zero_iff_nil in H2. subst.
  constructor. prove_term.
  intros. destruct H2.
  destruct clock0; inversion H2. destruct clock0; inversion H3. constructor.
Qed. *)

Proposition var_funid_eqb_neq (v0 v : Var + FunctionIdentifier):
    var_funid_eqb v0 v = false <-> v0 <> v.
  Proof.
    split; intros.
    { destruct v0, v.
      * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. reflexivity.
      * unfold not. intro. inversion H0.
      * unfold not. intro. inversion H0.
      * destruct f, f0. simpl in H. apply Bool.andb_false_iff in H. inversion H.
        - apply eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
        - apply Nat.eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
    }
    { destruct v0, v.
      * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff.
        unfold not in H. case_eq ((s =? s0)%string); intros.
        - right. apply String.eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst. reflexivity.
        - left. reflexivity.
    }
  Qed.

  Proposition var_funid_eqb_refl (var : Var + FunctionIdentifier) :
  var_funid_eqb var var = true.
  Proof.
    destruct var.
    * simpl. apply String.eqb_refl.
    * destruct f. simpl. rewrite String.eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  Qed.

  Proposition var_funid_eqb_sym (v1 v2 : Var + FunctionIdentifier) :
    var_funid_eqb v1 v2 = var_funid_eqb v2 v1.
  Proof.
    destruct v1, v2.
    * simpl. rewrite eqb_sym. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct f, f0. simpl. rewrite eqb_sym, Nat.eqb_sym. reflexivity.
  Qed.
  
  Proposition var_funid_eqb_eq (v0 v : Var + FunctionIdentifier):
    var_funid_eqb v0 v = true <-> v0 = v.
  Proof.
    intros. split; intros.
    { destruct v0, v.
      * inversion H. apply String.eqb_eq in H1. subst. reflexivity.
      * inversion H.
      * inversion H.
      * inversion H. destruct f, f0. inversion H1. apply Bool.andb_true_iff in H2. inversion H2.
        apply String.eqb_eq in H0. apply Nat.eqb_eq in H3. subst. reflexivity.
    }
    { destruct v, v0.
      * inversion H. subst. simpl. apply String.eqb_refl.
      * inversion H.
      * inversion H.
      * inversion H. simpl. destruct f. simpl. rewrite String.eqb_refl, Nat.eqb_refl. simpl. reflexivity.
    }
  Qed.

Module EnvFacts := WFacts_fun VarFunid_as_OT Environment.

Proposition get_value_here (env : Env) (var : Var + FunctionIdentifier) (val : Value):
Environment.find var (Environment.add var val env) = Some val.
Proof.
  apply EnvFacts.add_eq_o. auto.
Qed.

(** Previous append result *)
Proposition get_value_there (env : Env) (var var' : Var + FunctionIdentifier) 
     (val : Value):
var <> var' ->
Environment.find var' (Environment.add var val env) = Environment.find var' env.
Proof.
  apply EnvFacts.add_neq_o.
Qed.

(* equivalent, substitutional semantics would be better *)
Lemma foo env x :
  eval_env (S (S (S (S (S (S (S (S (S x))))))))) env (sum 2) = Res (VLit 3).
Proof.
  remember (S (S (S (S (S (S x)))))) as xx. simpl.
  rewrite get_value_here. rewrite Heqxx.
  remember (S (S (S x))) as xxx. unfold append_vars_to_env. simpl. rewrite get_value_here.
  rewrite get_value_there, get_value_here. 2: congruence. rewrite Heqxxx. simpl.
  rewrite get_value_here. unfold append_vars_to_env. simpl. rewrite get_value_here.
  rewrite get_value_there, get_value_here. 2: congruence. simpl.
Admitted.

Goal equiv_rel (sum 2) (ELit 3).
Proof.
  start_equiv. unfold sum.
  split; intros. eexists. exists 10. reflexivity.
  eexists. eexists. apply foo.
  intros. destruct H. destruct clock; inversion H0. subst.
Admitted.



(** Congruence *)

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

Theorem equiv_env_insert :
  forall env env',
  equiv_env env env' ->
  forall var v v', val_rel v v' -> equiv_env (insert_value env var v) (insert_value env' var v').
Proof.

Admitted.

Theorem equiv_env_app vars :
  forall vals env env',
  equiv_env env env' -> equiv_env (append_vars_to_env vars vals env) (append_vars_to_env vars vals env').
Proof.
  induction vars; intros.
  * simpl. destruct vals; auto.
  * simpl. destruct vals; auto. apply IHvars. apply equiv_env_insert; auto. constructor.
Qed.


Theorem equiv_rel_cong :
  forall (C : Context) (e1 e2 : Exp),
  equiv_rel e1 e2
->
  equiv_rel (C[[e1]]) (C[[e2]]).
Proof.
  induction C; intros.
  * simpl. auto.
  * simpl. constructor. prove_term.
    intros. destruct H1. destruct clock; inversion H1. inversion H2. constructor.
  * simpl. constructor.
    - split; intros; eapply equiv_env_term; try exact H0. 2: exact (equiv_env_sym _ _ H0). auto. auto.
    - intros. destruct H1.
      pose (equiv_env_eval _ _ _ _ _ H0 H1). destruct e, H3. rewrite H3 in H2. inversion H2. subst. auto.
  * simpl. constructor.
    - split; intros; eapply equiv_env_term; try exact H0. 2: exact (equiv_env_sym _ _ H0). auto. auto.
    - intros. destruct H1.
      pose (equiv_env_eval _ _ _ _ _ H0 H1). destruct e, H3. rewrite H3 in H2. inversion H2. subst. auto.
  * constructor. prove_term.
    intros. destruct H1. destruct clock; inversion H1. inversion H2.
    constructor. auto.
    intros. apply IHC. exact H. apply equiv_env_app. auto.
  * constructor. prove_term.
    intros. destruct H1. destruct clock; inversion H1. inversion H2. (* cofix alma. *) (** possible coinduction needed *)
    (* TODO: OR, which is better: finite unfolding *)
    constructor. auto.
    intros. (* constructor. *) apply IHC; auto. apply equiv_env_app. apply equiv_env_insert. auto.
    admit.
  * admit. (* wrong induction is generated for app, hand written is needed *)
  * simpl. pose (IHC1 e1 e2 H). unfold equiv_rel in e. constructor.
    - split; intros; destruct H1, H1, x0; inversion H1; break_match_hyp; try congruence.
      pose (e _ _ H0). remember e0 as C1HYP. clear e0 HeqC1HYP e. inversion C1HYP. subst.
      destruct H2.
      eexists. exists (S x0).
      simpl.

Admitted.


(*
F := fun(X, Y) -> X(Y)

F(fun(X) -> X, 1)
F(fun(X) -> X + 1 - 1, 1) 
*)

(**

(** Two events are A-related if they agree on all V-related values. *)
Definition A_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (Event (val τ)) :=
  fun A0 A1 =>
    forall v0 v1 (Hv : V_rel_τ v0 v1),
      (A0 v0 = (* iff *) A1 v1).
Inductive val_rel : Value -> Value -> Prop :=
| refl_rel v : val_rel v v
| clos_rel vl env b vl' env' b' :
  length vl = length vl' ->
  (forall vals, length vals = length vl ->
  exp_rel (append_vars_to_env vl vals env) (append_vars_to_env vl' vals env') b b')
->
  val_rel (VFun env vl b) (VFun env' vl' b')
| rec_clos_rel f vl env b f' vl' env' b' :
  length vl = length vl' ->
  (forall vals, length vals = length vl ->
  exp_rel (append_vars_to_env vl vals (insert_value env (inr f) (VRecFun env f vl b))) (append_vars_to_env vl' vals (insert_value env' (inr f') (VRecFun env' f' vl' b'))) b b')
->
  val_rel (VRecFun env f vl b) (VRecFun env' f' vl' b')
with exp_rel : Environment -> Environment -> Exp -> Exp -> Prop :=
| exp_rel_cons env env' e1 e2:
  (terminating e1 env <-> terminating e2 env') ->
  (forall v1 v2 clock,
      eval_env clock env e1 = Res v1 /\
      eval_env clock env' e2 = Res v2 ->
      val_rel v1 v2)
->
  exp_rel env env' e1 e2
.
*)

(*
(** Two closed expressions are E-related if their value measures agree for all
    A-related events. *)
Definition E_rel' (τ : Ty) (V_rel_τ : relation (val τ)) : relation (expr · τ) :=
  fun e0 e1 =>
    forall A0 A1 (HA : A_rel' τ V_rel_τ A0 A1),
      μ e0 A0 = μ e1 A1.*)

(* Future work, based on https://github.com/cobbal/ppl-ctx-equiv-coq 
  Trick: avoid positivity check by using typing
*)

Definition E_rel (V_rel : relation Value) (env env' : Environment) (e1 e2 : Exp) : Prop :=
  ((terminating e1 env) <-> (terminating e2 env')) /\
  (forall clock v1 v2,
    eval_env clock env e1 = Res v1 /\
    eval_env clock env' e2 = Res v2 ->
    V_rel v1 v2)
.

Lemma E_rel_refl : forall (V_rel : relation Value)(env env : Environment),
  Reflexive V_rel
->
  Reflexive (E_rel V_rel env env).
Proof.
  intros. unfold Reflexive, E_rel in *. intros. split.
  * split; intros; auto.
  * intros. destruct H0. rewrite H0 in H1. inversion H1. subst. apply H.
Qed.

Lemma E_rel_sym : forall (V_rel : relation Value)(env env' : Environment),
  Symmetric V_rel
->
  (forall e e', E_rel V_rel env env' e e' -> E_rel V_rel env' env e' e).
Proof.
  intros. unfold Symmetric, E_rel in *. destruct H0. intros. split.
  * symmetry. auto.
  * intros. destruct H2. apply H. eapply H1. split. exact H3. auto.
Qed.

Lemma E_rel_trans : forall (V_rel : relation Value)(env env' env'' : Environment),
  Transitive V_rel
->
  (forall e e' e'', E_rel V_rel env env' e e' -> E_rel V_rel env' env'' e' e''
  ->
  E_rel V_rel env env'' e e'').
Proof.
  intros. unfold Transitive, E_rel in *. destruct H0, H1. intros. split.
  * eapply iff_trans. exact H0. auto.
  * intros. destruct H4, H0, H1. assert (exists v3 clock, eval_env clock env' e' = Res v3).
    { apply H0. eexists. eexists. exact H4. }
    destruct H8, H8.
    apply bigger_clock with (clock' := clock + x0) in H4.
    apply bigger_clock with (clock' := clock + x0) in H8.
    apply bigger_clock with (clock' := clock + x0) in H5. 2-4: lia.
    pose (H2 _ _ _ (conj H4 H8)). pose (H3 _ _ _ (conj H8 H5)). eapply H. exact v. auto.
Qed.

Definition V_rel_num : relation Z := eq.
Inductive V_rel_fun (valr : relation Value) : relation Value :=
| clos_rel2 vl env b vl' env' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> valr (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0))) ->
  E_rel valr (append_vars_to_env vl vals1 env) (append_vars_to_env vl' vals2 env') b b')
->
  V_rel_fun valr (VFun env vl b) (VFun env' vl' b')
(** TODO: recfun *)
| rec_clos_rel2 f vl env b f' vl' env' b' :
  length vl = length vl' ->
  (forall vals1 vals2, length vals1 = length vl -> length vals2 = length vl' ->
    (forall i, i < length vl -> valr (nth i vals1 (VLit 0)) (nth i vals2 (VLit 0))) ->
  E_rel valr (append_vars_to_env vl vals1 (insert_value env (inr f) (VRecFun env f vl b)))
             (append_vars_to_env vl' vals2 (insert_value env' (inr f) (VRecFun env' f' vl' b'))) b b')
->
  V_rel_fun valr (VRecFun env f vl b) (VRecFun env' f' vl' b')
.

(* Unset Positivity Checking. *)

(* THe problem is not with endlessly recursive closures, because:
  - their type would be a -> b, but b will not be extended! e.g. fun f X -> f X 
                                     this is an application, not a closure  ^^^^
  Probematic:
  fun X -> fun X -> fun X -> .... <- however, this will be finite, because terms are finite
  thus, we can take a natural number to measure the size instead of typing
    ~> this number is decreased by applications, and increased by function definitions
    - Idea: it should be the size of the term?
*)

(* Inductive v_rel : relation Value :=
| rel_v v1 v2 : V_rel_refl v1 v2 -> v_rel v1 v2
| rel_clos env env' vl vl' b b' : V_rel_fun v_rel (VFun env vl b) (VFun env' vl' b')
  ->
    v_rel (VFun env vl b) (VFun env' vl' b')
.*)

Fixpoint v_rel (n : nat) : relation Value :=
fun v1 v2 =>
match n with
| 0 => False
| S n' =>
  match v1, v2 with
  | VLit n, VLit m => V_rel_num n m
  | VFun _ _ _, VFun _ _ _ => V_rel_fun (v_rel n') v1 v2
  | VRecFun _ _ _ _, VRecFun _ _ _ _ => V_rel_fun (v_rel n') v1 v2
  | _, _ => False
  end
end.

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
  fun v1 v2 => v_rel (val_size v1 + val_size v2) v1 v2.




(* TODO: Here, we could say exists a nat, which is the parameter of v_rel, if needed *)
Definition eq_env : relation Environment :=
 fun env env' =>
  length env = length env' /\
  forall i, i < length env -> val_rel_size (snd (nth i env (inl "X"%string, VLit 0))) (snd (nth i env' (inl "X"%string, VLit 0))) /\ fst (nth i env (inl "X"%string, VLit 0)) = fst (nth i env' (inl "X"%string, VLit 0)).


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



