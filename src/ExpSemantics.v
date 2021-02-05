Require Export ExpSyntax.
From Coq Require Export micromega.Lia.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Import ListNotations.

Section functional_semantics.

Fixpoint eval_list (f : Exp -> option Exp) (l : list Exp) : option (list Exp) :=
match l with
| [] => Some []
| x::xs => match f x with
           | Some v => match eval_list f xs with
                       | Some vs => Some (v::vs)
                       | None => None
                       end
           | None => None
           end
end.

Fixpoint eval (clock : nat) (e : Exp) : option Exp :=
match clock with
| 0 => None
| S n => match e with
         | ELit l => Some (ELit l)
         | EVar v => None
         | EFunId f => None
         | EFun vl e => Some (EFun vl e)
         | ERecFun f vl e => Some (ERecFun f vl e)
         | EApp exp l => match eval n exp with
                         (** In Core Erlang this check only happens later *)
                         | Some (EFun vl e) =>
                            (* This would be better with Monads *)
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Some vals => eval n (varsubst_list vl vals e)
                               | None => None
                               end
                         | Some (ERecFun f vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Some vals => eval n (funsubst f (ERecFun f vl e) (varsubst_list vl vals e))
                               | None => None
                               end
                         | _ => None
                         end
         | ELet v e1 e2 => match eval n e1 with
                           | Some val => eval n (varsubst v val e2)
                           | _      => None
                           end
         | ELetRec f vl b e => eval n (funsubst f (ERecFun f vl b) e)
         | EPlus e1 e2 => 
            match eval n e1, eval n e2 with
            | Some (ELit n), Some (ELit m) => Some (ELit (n + m))
            | _, _ => None
            end
         | EIf e1 e2 e3 =>
            match eval n e1 with
            | Some (ELit 0) => eval n e2
            | Some _        => eval n e3
            | None          => None
            end
        end
end.

(** Tests: *)

Goal eval 10 (inc 2) = Some (ELit 3). Proof. auto. Qed.
Goal eval 10 (simplefun 10) = Some (ELit 10). Proof. simpl. auto. Qed.
Goal eval 10 (sum 2) = Some (ELit 3). Proof. simpl. auto. Qed.
Goal eval 100 (sum 10) = Some (ELit 55). Proof. simpl. auto. Qed.
Goal eval 100 (simplefun2 10 10) = Some (ELit 20). Proof. simpl. auto. Qed.

End functional_semantics.


(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)
Section stack_machine_semantics.

Inductive is_value : Exp -> Prop :=
| ELit_val : forall l, is_value (ELit l)
| EFun_val : forall vl e, is_value (EFun vl e)
| ERecFun_val : forall f vl e, is_value (ERecFun f vl e).



Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (p : is_value v) (l1 l2 : list Exp) (p2 : forall e, In e l2 -> is_value e) (** Can be problematic *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (p : is_value v) (* v + □ *)
| FIf (e2 e3 : Exp) (* if □ then e2 else e3 *).

Definition FrameStack := list Frame.

Lemma empty_is_value : forall e, In e [] -> is_value e. Proof. firstorder. Qed.
Lemma step_value : forall l v,
  (forall e, In e l -> is_value e) -> is_value v
->
  (forall e, In e (l ++ [v]) -> is_value e).
Proof.
  intros. apply in_app_or in H1. destruct H1.
  * apply H. auto.
  * firstorder. subst. auto.
Qed.

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_app_start v hd tl xs (H : is_value v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v H tl [] empty_is_value)::xs, hd⟩

| red_app_fin xs e :
  ⟨ (FApp1 [])::xs, EFun [] e ⟩ --> ⟨ xs, e ⟩

| red_rec_app_fin xs e f :
  ⟨ (FApp1 [])::xs, ERecFun f [] e ⟩ --> ⟨ xs, funsubst f (ERecFun f [] e) e ⟩

| app2_step v H hd tl vs H2 xs v' (H' : is_value v') :
  ⟨ (FApp2 v H (hd::tl) vs H2) :: xs, v' ⟩ --> ⟨ (FApp2 v H tl (vs ++ [v']) (step_value vs v' H2 H')) :: xs, hd ⟩

| red_app2 vl e vs v xs H H2 : 
  is_value v ->
  ⟨ (FApp2 (EFun vl e) H [] vs H2) :: xs, v ⟩ --> ⟨ xs,  varsubst_list vl (vs ++ [v]) e ⟩

| red_rec_app2 vl f e vs v xs H H2 : 
  is_value v ->
  ⟨ (FApp2 (ERecFun f vl e) H [] vs H2) :: xs, v ⟩ --> ⟨ xs,  funsubst f (ERecFun f vl e) (varsubst_list vl (vs ++ [v]) e) ⟩

| red_let v val e2 xs (H : is_value val) : ⟨ (FLet v e2)::xs, val ⟩ --> ⟨ xs, varsubst v val e2⟩

| red_if_true e2 e3 xs : ⟨ (FIf e2 e3)::xs, ELit 0 ⟩ --> ⟨ xs, e2 ⟩

| red_if_false e2 e3 v xs (H : is_value v) :
  v <> ELit 0 ->
  ⟨ (FIf e2 e3)::xs, v ⟩ --> ⟨ xs, e3 ⟩

| red_plus_left e2 xs v (H : is_value v): ⟨ (FPlus1 e2)::xs, v ⟩ --> ⟨ (FPlus2 v H)::xs, e2 ⟩

| red_plus_right xs n m P :
   ⟨ (FPlus2 (ELit n) P)::xs, (ELit m) ⟩ --> ⟨ xs, ELit (n + m) ⟩ 

| red_letrec xs f vl b e:
  ⟨ xs, ELetRec f vl b e ⟩ --> ⟨ xs, funsubst f (ERecFun f vl b) e ⟩

(** Steps *)
| step_let xs v e1 e2 : ⟨ xs, ELet v e1 e2 ⟩ --> ⟨ (FLet v e2)::xs, e1 ⟩
| step_app xs e el: ⟨ xs, EApp e el ⟩ --> ⟨ (FApp1 el)::xs, e ⟩
| step_plus xs e1 e2 : ⟨ xs, EPlus e1 e2⟩ --> ⟨ (FPlus1 e2)::xs, e1⟩
| step_if xs e1 e2 e3 : ⟨ xs, EIf e1 e2 e3⟩ --> ⟨ (FIf e2 e3)::xs, e1⟩
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

Reserved Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
| step_refl e : is_value e -> ⟨ [], e ⟩ -->* ⟨ [], e ⟩
| step_trans fs e fs' e' fs'' e'' :
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -->* ⟨fs'', e''⟩
->
  ⟨ fs, e ⟩ -->* ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_rt fs e fs' e').

Goal ⟨ [], inc 1 ⟩ -->* ⟨[], ELit 2⟩.
Proof.
  repeat econstructor.
  Unshelve. simpl. constructor.
Qed.

Goal ⟨ [], simplefun 10 ⟩ -->* ⟨[], ELit 10⟩.
Proof.
  (* repeat econstructor. <- this works too *)
  unfold simplefun.
  apply step_trans with (fs' := [FLet XVar (EApp (EVar XVar) [])])
                        (e' := EFun [] (ELit 10)).
  * apply step_let.
  * apply step_trans with (fs' := []) (e' := EApp (EFun [] (ELit 10)) []).
    - apply red_let. constructor.
    - apply step_trans with (fs' := [FApp1 []]) (e' := EFun [] (ELit 10)).
      + apply step_app.
      + econstructor.
        ** apply red_app_fin.
        ** apply step_refl. constructor.
Qed.

Goal ⟨ [], simplefun2 10 10 ⟩ -->* ⟨[], ELit 20⟩.
Proof.
  unfold simplefun2.
  repeat econstructor.
  Unshelve.
  all : try constructor.
Qed.

Goal ⟨ [], sum 1 ⟩ -->* ⟨[], ELit 1⟩.
Proof.
  unfold sum.
  econstructor.
  econstructor.
  simpl.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eapply red_rec_app2. constructor.
  simpl. econstructor. eapply step_if.
  econstructor. eapply red_if_false. constructor. congruence.
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
  simpl. econstructor. eapply step_if.
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
  * inversion H1; subst; try inversion H0; auto.
  * inversion H1; subst; auto; try inversion H0.
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

Theorem step_rt_determinism {e v fs} :
  ⟨fs, e⟩ -->* ⟨ [] , v ⟩ -> is_value v
->
  (forall fs'' v', ⟨fs, e⟩ -->* ⟨fs'', v'⟩ -> fs'' = [] /\ v' = v).
Proof.
  intro. dependent induction H; intros.
  * inversion H1; subst.
    - auto.
    - eapply value_nostep in H2. contradiction. auto.
  * inversion H2; subst.
    - apply value_nostep in H. contradiction. auto.
    - pose (step_determinism H _ _ H3). destruct a. subst. apply IHstep_rt; auto.
Qed.

End stack_machine_semantics.