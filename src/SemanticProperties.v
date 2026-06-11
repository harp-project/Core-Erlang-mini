From CoreErlang Require Import SubstSemantics.


(** Example, simple evaluations *)
Open Scope Z_scope.
Goal ⟨ [], inc 1 ⟩ -->* VLit 2.
Proof.
  repeat (econstructor;cbn).
Qed.

Local Goal ⟨ [], simplefun 10 ⟩ -->* VLit 10.
Proof.
  repeat econstructor.
Qed.

Local Goal ⟨ [], simplefun2 10 10 ⟩ -->* VLit 20.
Proof.
  unfold simplefun2.
  repeat econstructor.
  all: inversion H; subst; cbn in *; auto.
  all: inversion H1; subst; cbn in *; auto; lia.
Qed.

Local Goal ⟨ [], sum 1 ⟩ -->* VLit 1%Z.
Proof.
  unfold sum.
  simpl.
  econstructor. econstructor. econstructor.
  econstructor. simpl.
  econstructor.
  econstructor. econstructor. cbn. econstructor. constructor. auto.
  econstructor.
  eapply red_app2. constructor.
  simpl. econstructor. econstructor. econstructor. cbn. eapply red_case_false. constructor.
  econstructor. eapply step_bif.
  econstructor. eapply red_bif_start; auto.
  econstructor. eapply red_bif_step; auto.
  econstructor. cbn. eapply step_app.
  econstructor. eapply red_app_start. auto.
  econstructor.
  eapply step_bif.

  econstructor. eapply red_bif_start; auto.
  econstructor. eapply red_bif_step; auto. simpl.
  econstructor. eapply red_plus; auto. simpl.
  econstructor. eapply red_app2. constructor.
  simpl. econstructor. econstructor. econstructor. cbn.
  eapply red_case_true. constructor.
  econstructor. eapply red_plus.
  econstructor.
Qed.

Local Goal ⟨[], ECons (EBIF (VLit "+"%string) [˝VLit 1; ˝VLit 1]) (ECons (VLit 1) (ECons (VLit 0) VNil))⟩ -->* VCons (VLit 2) (VCons (VLit 1) (VCons (VLit 0) VNil)).
Proof.
  exists 13%nat.
  econstructor. constructor.
  econstructor. apply step_cons.
  econstructor. apply step_cons. econstructor. constructor.
  econstructor. constructor; constructor.
  econstructor. constructor. repeat constructor.
  econstructor. constructor; repeat constructor.
  econstructor. constructor. repeat constructor.
  econstructor. apply step_bif.
  econstructor. constructor.
  econstructor. constructor.
  econstructor. constructor.
  repeat econstructor.
Qed.

(** Complex example for map *)
Local Goal
   ⟨[], obj_map (VFun 1 (EBIF (VLit "+"%string) [˝VVar 1; ˝VLit 1]))
                (ECons (VLit 0) (ECons (VLit 1) (ECons (VLit 2) VNil)))⟩ -->*
   VCons (VLit 1) (VCons (VLit 2) (VCons (VLit 3) VNil)).
Proof.
  exists 65%nat.

  (** evaluate letrec *)
  econstructor. constructor. simpl.

  (** start application evaluation *)
  econstructor. constructor. simpl.
  econstructor. constructor. auto.

  (** function parameter *)
  econstructor. constructor; auto; simpl.
  econstructor. constructor; auto; simpl.

  (** evaluate list to value list *)
  simpl.
  econstructor. apply step_cons; auto.
  econstructor. apply step_cons; auto.
  econstructor. apply step_cons; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto.

  (** process first element in the recursive call *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. simpl.

  (** process second element in the recursive call *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. simpl.

  (** process third element in the recursive call *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. simpl.

  (** stop recursion with VNil *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. apply red_case_false; auto.

  (** apply function to the third element *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.

  (** apply function to the second element *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.

  (** apply function to the first element *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.
  constructor.
Qed.

(** Complex example for foldr *)
Local Goal
   ⟨[], obj_foldr
                (VFun 2 (ECons (EBIF (VLit "+"%string) [˝VVar 1; ˝VLit 1]) (VVar 2)))
                (ECons (VLit 0) (ECons (VLit 1) (ECons (VLit 2) VNil))) VNil⟩ -->*
   VCons (VLit 1) (VCons (VLit 2) (VCons (VLit 3) VNil)).
Proof.
  exists 72%nat.

  (** Evaluate letrec *)
  econstructor. constructor. simpl.

  (** Application with 3 params *)
  econstructor. constructor. simpl.
  econstructor. constructor. auto.
  econstructor. constructor; auto. simpl.
  econstructor. constructor; auto.
  econstructor. constructor; auto.

  (** evaluate parameter list to list of values *)
  econstructor. apply step_cons; auto.
  econstructor. apply step_cons; auto.
  econstructor. apply step_cons; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto.
  econstructor. apply red_cons1; auto.
  econstructor. apply red_cons2; auto. simpl.

  (** apply recursive call with the first element *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. cbn.

  (** apply recursive call with the second element *)
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. cbn.

  (** apply recursive call with the third element *)
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto.
  econstructor. apply step_app.
  econstructor. constructor. auto.
  econstructor. constructor; auto. cbn.

  (** end of recursion with VNil *)
  econstructor. apply step_app.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. apply red_case_false; auto.

  (** build the list back, by applying the +1 BIF *)
  (** 3rd element *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_cons.
  econstructor. constructor; auto.
  econstructor. apply step_bif.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  (** 2nd element *)
  econstructor. apply step_cons.
  econstructor. constructor. auto.
  econstructor. apply step_bif.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  (** 1st element *)
  econstructor. apply step_cons.
  econstructor. constructor; auto.
  econstructor. apply step_bif.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  constructor.
Qed.

Definition computes (e : Exp) (f : Val -> Val) :=
  forall v, ⟨[], EApp (VFun 1 e) [˝v]⟩ -->* f v.

Fixpoint cons_to_list (e : Val) : option (list Val) :=
match e with
| VNil => Some []
| VCons e1 e2 => match cons_to_list e2 with
                 | Some e2'=> Some (e1 :: e2')
                 | _ => None
                 end
| _ => None
end.

Fixpoint list_to_cons (l : list Val) : Val :=
match l with
| [] => VNil
| e1 :: xs => VCons e1 (list_to_cons xs)
end.

Ltac proof_irr :=
match goal with
| [H1 : ?P, H2 : ?P |- _] => assert (H1 = H2) by apply proof_irrelevance; subst
end.
Ltac proof_irr_many := repeat proof_irr.

(** Properties of the semantics *)
Theorem step_determinism {e e' fs fs'} :
  ⟨ fs, e ⟩ --> ⟨fs', e'⟩ ->
  (forall fs'' e'', ⟨fs, e⟩ --> ⟨fs'', e''⟩ -> fs'' = fs' /\ e'' = e').
Proof.
  intro H. dependent induction H; intros.
  all: try by inv H.
  all: try by inv H0.
Qed.

Theorem value_nostep (v : Val) :
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  dependent induction v; intros.
  * inversion H.
  * inversion H.
  * inversion H.
  * inversion H.
  * inversion H.
  * inversion H.
Qed.

Theorem step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩
->
  (forall fs'' v', ⟨fs, e⟩ -[k]-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intro. dependent induction H; intros.
  * inversion H; subst; auto.
  * inversion H1; subst. apply IHstep_rt; auto. eapply step_determinism in H; eauto. destruct H. subst. auto.
Qed.


Ltac destruct_scope :=
match goal with
| [H : EXP _ ⊢ VVal _ |- _] => inv H
| [H : EXP _ ⊢ EExp _ |- _] => inv H
| [H : VAL _ ⊢ VLit _ |- _] => inv H
| [H : VAL _ ⊢ VPid _ |- _] => inv H
| [H : VAL _ ⊢ VVar _ |- _] => inv H
| [H : VAL _ ⊢ VFun _ _ |- _] => inv H
| [H : VAL _ ⊢ VNil |- _] => inv H
| [H : VAL _ ⊢ VCons _ _ |- _] => inv H
| [H : NVAL _ ⊢ EApp _ _ |- _] => inv H
| [H : NVAL _ ⊢ ELet _ _ |- _] => inv H
| [H : NVAL _ ⊢ ECase _ _ _ _ |- _] => inv H
| [H : NVAL _ ⊢ ECons _ _ |- _] => inv H
| [H : NVAL _ ⊢ EReceive _ |- _] => inv H
| [H : NVAL _ ⊢ EBIF _ _ |- _] => inv H
| [H : FCLOSED _ |- _] => inv H
| [H : FSCLOSED (_ :: _) |- _] => inv H
| [H : FSCLOSED [] |- _] => inv H
| [H : Forall _ (_ :: _) |- _] => inv H
| [H : Forall _ [] |- _] => inv H
end.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FSCLOSED F -> EXPCLOSED e
->
  FSCLOSED F' /\ EXPCLOSED e'.
Proof.
  intros F e F' e' Hstep.
  induction Hstep; intros HFs Hclosed; repeat destruct_scope.
  all: split; repeat constructor; try by assumption.
  * apply -> subst_preserves_scope_exp. eassumption.
    intro. intros. destruct v. 2: lia. simpl. by constructor.
  * apply Forall_app. split. assumption. by constructor.
  * apply -> subst_preserves_scope_exp. eassumption.
    pose proof scoped_list_idsubst ((VFun (S (length vs)) e :: vs ++ [v])).
    replace (length (_ :: _)) with (S (S (length vs)) + 0)%nat in H.
    2: simpl; rewrite length_app; simpl; lia. apply H.
    constructor. by constructor.
    apply Forall_app. split. assumption.
    by constructor.
  * apply Forall_app. split. assumption. by constructor.
  * apply -> subst_preserves_scope_exp. eassumption.
    intro. intros. destruct v. 2: lia. simpl. assumption.
  * apply -> subst_preserves_scope_exp. eassumption.
    pose proof (match_pattern_scoped _ _ _ _ H1 H) as X.
    pose proof scoped_list_idsubst l _ X.
    erewrite match_pattern_length; eassumption.
  * eapply indexed_to_forall. eassumption.
  * eapply indexed_to_forall. eassumption.
  * by rewrite Nat.add_0_r in H5.
Qed.

Corollary step_any_closedness : forall F e v,
   ⟨ F, e ⟩ -->* v -> FSCLOSED F -> EXPCLOSED e
->
  VALCLOSED v.
Proof.
  intros. destruct H. dependent induction H.
  * by inversion H1.
  * apply step_closedness in H as []; auto.
Qed.

Definition terminates_sem (fs : FrameStack) (e : Exp) : Prop :=
  exists v, ⟨fs, e⟩ -->* v.

Definition terminates_in_k_sem (fs : FrameStack) (e : Exp) (k : nat) : Prop :=
  exists v : Val, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.

Open Scope nat_scope.

(** Inductively defined termination relation. This will be used by the
    equivalence concepts (CIU, CTX, logical relations).
*)
Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Exp -> nat -> Prop :=

| term_value (v : Val) : | [] , v | 0 ↓
| term_case_true fs e1 e2 k v p l :
  match_pattern p v = Some l -> | fs , e1.[list_subst l idsubst] | k ↓
 ->
  | (FCase p e1 e2)::fs , v | S k ↓
| term_case_false fs e1 e2 v k p :
  match_pattern p v = None -> | fs , e2 | k ↓ 
 -> 
  | (FCase p e1 e2)::fs , v | S k ↓
| term_let_subst v e2 fs k : | fs, e2.[v/] | k ↓ -> | (FLet e2)::fs, v | S k ↓
| term_app_start v hd tl fs k : 
  | (FApp2 v [] tl)::fs, hd| k ↓ -> | (FApp1 (hd::tl))::fs, v | S k ↓
| term_bif_start v hd tl fs k : 
  | (FBIF2 v [] tl)::fs, hd| k ↓ -> | (FBIF1 (hd::tl))::fs, v | S k ↓
| term_app_fin e fs k : | fs, e.[VFun 0 e/] | k ↓ -> | (FApp1 [])::fs, VFun 0 e | S k ↓
| term_app_step v v' hd tl vs fs k :
  | (FApp2 v (vs ++ [v']) tl)::fs, hd | k ↓ -> | (FApp2 v vs (hd::tl))::fs , v' | S k ↓
| term_bif_step v v' hd tl vs fs k :
  | (FBIF2 v (vs ++ [v']) tl)::fs, hd | k ↓ -> | (FBIF2 v vs (hd::tl))::fs , v' | S k ↓
| term_plus (i1 i2 : Z) fs k :
  | fs, VLit (Z.add i1 i2) | k ↓ ->
  | (FBIF2 (VLit "+"%string) [VLit (Int i1)] [])::fs, VLit (Int i2) | S k ↓

| term_app2 v vl e vs fs k :
  vl = S (length vs) -> | fs, e.[list_subst (VFun vl e  :: (vs ++ [v])) idsubst] | k ↓ 
-> | (FApp2 (VFun vl e) vs [])::fs, v | S k ↓
| term_cons1 e1 v2 fs k:
  | FCons2 v2::fs, e1 | k ↓ -> | FCons1 e1 :: fs, v2 | S k ↓
| term_cons2 v1 v2 fs k :
  | fs, VCons v1 v2 | k ↓ -> | FCons2 v2 :: fs, v1 | S k ↓

| term_case e e1 e2 fs k p : | (FCase p e1 e2)::fs, e | k ↓ -> | fs, ECase e p e1 e2 | S k ↓
| term_app e vs fs k : | (FApp1 vs)::fs, e | k ↓ -> | fs, EApp e vs | S k ↓
| term_bif e vs fs k : | (FBIF1 vs)::fs, e | k ↓ -> | fs, EBIF e vs | S k ↓
| term_let e1 e2 fs k : | (FLet e2)::fs, e1 | k ↓ -> | fs, ELet e1 e2 | S k ↓
| term_cons fs e1 e2 k :
  | FCons1 e1 :: fs, e2 | k ↓ -> | fs, ECons e1 e2 | S k ↓
where "| fs , e | k ↓" := (terminates_in_k fs e k).

Definition terminates (fs : FrameStack) (e : Exp) := exists n, | fs, e | n ↓.
Notation "| fs , e | ↓" := (terminates fs e) (at level 80).

Theorem terminates_in_k_eq_terminates_in_k_sem :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  split.
  * intros [v Hrt].
    remember [] as fs' eqn:Hfs in Hrt.
    remember (˝ v) as e' eqn:He in Hrt.
    induction Hrt.
    - inversion Hfs; inversion He; subst. constructor.
    - subst. dependent destruction H; eauto using terminates_in_k.
  * intros Hterm. induction Hterm.
    exists v. apply step_refl.
    all: destruct IHHterm as [w Hrt]; exists w; econstructor; [econstructor; eauto | exact Hrt].
Qed.

Corollary terminates_eq_terminates_sem :
  forall e fs, terminates_sem fs e <-> | fs, e | ↓.
Proof.
  split; intros.
  * destruct H as [v [k Hrt]]. exists k.
    apply terminates_in_k_eq_terminates_in_k_sem. exists v. exact Hrt.
  * destruct H as [k Hterm].
    apply terminates_in_k_eq_terminates_in_k_sem in Hterm.
    destruct Hterm as [v Hrt]. exists v. exists k. exact Hrt.
Qed.

Theorem terminates_step :
  forall fs e, | fs, e | ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | ↓.
Proof.
  intros fs e Hterm fs' e' Hstep.
  apply terminates_eq_terminates_sem in Hterm.
  destruct Hterm as [v [k Hrt]].
  destruct k.
  * inversion Hrt. subst. apply value_nostep in Hstep; intuition.
  * inversion Hrt as [| fs0 e0 fs1 e1 fs2 e2 k' Hstep' Hrt']; subst.
    apply (step_determinism Hstep) in Hstep'. destruct Hstep'. subst.
    apply terminates_eq_terminates_sem. exists v. eexists. exact Hrt'.
Qed.

Theorem terminates_step_2 :
  forall n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | n - 1↓.
Proof.
  intros n fs e Hterm fs' e' Hstep.
  apply terminates_in_k_eq_terminates_in_k_sem in Hterm.
  destruct Hterm as [v Hrt]. destruct n.
  * inversion Hrt. subst. apply value_nostep in Hstep; intuition.
  * inversion Hrt as [| fs0 e0 fs1 e1 fs2 e2 k' Hstep' Hrt']; subst.
    apply (step_determinism Hstep) in Hstep'. destruct Hstep'. subst.
    apply terminates_in_k_eq_terminates_in_k_sem. exists v. now rewrite Nat.sub_1_r.
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
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0 as [v Hrt].
  pose proof (transitive_eval _ _ _ _ _ H _ _ _ Hrt). replace (k+(n-k)) with n in H0 by lia.
  eexists. exact H0.
Qed.

Corollary term_step_term_plus :
  forall k k2 fs e fs' e', 
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | k2 ↓
->
  | fs, e | k + k2 ↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem.
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0 as [v Hrt].
  pose proof (transitive_eval _ _ _ _ _ H _ _ _ Hrt).
  eexists. exact H0.
Qed.

Lemma eval_app_partial :
  forall vals vl e v Fs hds, vl = length (hds ++ v :: vals) ->
  ⟨ FApp2 (VFun vl e) hds (map VVal vals) :: Fs, v ⟩ -[S (length vals)]-> ⟨ Fs , e.[list_subst (VFun vl e :: (hds ++ v :: vals)) idsubst]⟩.
Proof.
  induction vals; intros.
  * simpl. econstructor. apply red_app2. rewrite length_app in H. simpl in H. lia.
    constructor.
  * simpl. econstructor. apply app2_step.
    assert (Hlen : vl = length ((hds ++ [v]) ++ a :: vals)).
    { rewrite <- app_assoc. exact H. }
    epose proof (IHvals vl e a _ (hds ++ [v]) Hlen) as H'.
    rewrite <- app_assoc in H'. exact H'.
Qed.

Lemma app1_eval :
  forall vals Fs vl e, vl = length vals ->
  exists k : nat,
  ⟨ [FApp1 (map VVal vals)] ++ Fs, VFun vl e ⟩ -[ k ]-> ⟨ Fs, e.[VFun vl e .: list_subst vals idsubst] ⟩.
Proof.
  destruct vals as [|a vals]; intros.
  * simpl in H. subst. exists 1. econstructor.
    simpl. apply red_app_fin. cbn. constructor.
  * exists (S (S (length vals))). simpl.
    eapply step_trans
      with (fs' := FApp2 (VFun vl e) [] (map VVal vals) :: Fs)
           (e' := a) (k := S (length vals));
      [apply red_app_start | apply eval_app_partial; exact H].
Qed.

Lemma eval_app_partial_core :
  forall (hds' : list Val) (vals : list Exp) vl e (e' : Exp) (v : Val) Fs hds,
  ⟨ FApp2 (VFun vl e) hds (map VVal hds' ++ e' :: vals) :: Fs, v ⟩ -[S (length hds')]-> 
  ⟨ FApp2 (VFun vl e) (hds ++ v :: hds') vals :: Fs , e'⟩.
Proof.
  induction hds'; intros.
  * simpl. econstructor. apply app2_step.
    constructor.
  * simpl. econstructor. apply app2_step.
    epose proof (IHhds' vals vl e _ a Fs (hds ++ [v])) as H'.
    rewrite <- app_assoc in H'. exact H'.
Qed.

Lemma full_eval_app_partial : forall e vals vl Fs,
  vl = length vals ->
  ⟨ Fs, EApp (VFun vl e) (map VVal vals) ⟩ -[2 + length vals]-> ⟨ Fs, e.[VFun vl e .: list_subst vals idsubst] ⟩.
Proof.
  destruct vals as [|a vals]; intros.
  - simpl in H. subst. econstructor. apply step_app.
    econstructor. apply red_app_fin. constructor.
  - simpl.
    eapply step_trans
      with (fs' := FApp1 (map VVal (a :: vals)) :: Fs)
           (e' := VFun vl e) (k := S (S (length vals)));
      [apply step_app |
       eapply step_trans
         with (fs' := FApp2 (VFun vl e) [] (map VVal vals) :: Fs)
              (e' := a) (k := S (length vals));
         [apply red_app_start | apply eval_app_partial; exact H] ].
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
  | FApp2 e' hds tl :: Fs, e | k ↓ ->
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Val) (k : nat), ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩)
->
  exists vl b, e' = VFun vl b /\ vl = S (length hds + length tl).
Proof.
  induction tl; intros.
  * pose proof H as Hterm.
    apply H0 in Hterm as [x [k0 Hrt]]. 2: lia.
    eapply terminates_step_any_2 in H. 2: exact Hrt.
    inversion H; subst; clear H; try congruence.
    all: try solve [do 2 eexists; split; [reflexivity| rewrite Nat.add_0_r; lia] ].
  * pose proof H as Hterm.
    apply H0 in Hterm as [x [k0 Hrt]]. 2: lia.
    eapply terminates_step_any_2 in H. 2: exact Hrt.
    inversion H; subst; clear H; try congruence.
    pose proof H2 as Hsub.
    apply H0 in H2 as [y [k2 Hrt2]]. 2: lia.
    eapply terminates_step_any_2 in Hsub; [| exact Hrt2 ].
    apply IHtl in Hsub. destruct Hsub as [? [? [Eq1 Eq2]]]. subst.
    do 2 eexists. split. reflexivity. rewrite length_app; simpl. lia.
    intros. eapply H0. 2: eassumption. lia.
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
  all: try (apply cons_neq in x; contradiction).
  all: symmetry in x; try (apply cons_cons_neq in x; contradiction).
Qed.

Theorem frame_indep_core : forall k e Fs Fs' v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k]-> ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  induction k; intros.
  * inversion H. subst. constructor.
  * inversion H. subst. inversion H1; subst.
    1-8, 10-17: simpl; econstructor; try constructor; auto.
    all: try (eapply IHk in H4; simpl in H4; exact H4); auto.
    econstructor. apply red_case_false; auto. apply IHk; auto.
Qed.

Theorem frame_indep_nil : forall k e Fs v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k]-> ⟨ Fs', v ⟩.
Proof.
  intros. eapply frame_indep_core in H. exact H.
Qed.

Lemma term_app_length : forall tl hds e k Fs x0,
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Val) (k : nat), ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩ /\ k <= m) ->
  | FApp2 x0 hds tl :: Fs, e | k ↓ -> k > length tl.
Proof.
  induction tl; intros.
  * inversion H0; simpl; lia.
  * simpl. apply H in H0 as H0'. 2: lia. destruct H0' as [? [? [? ?]]].
    eapply (terminates_step_any_2 _ _ _ _ H0) in H1 as H1'. inv H1'.
    eapply IHtl in H4. lia.
    intros. apply H. lia. assumption.
Qed.

(* Lemma eval_app_partial_core_2 :
  forall hds' vals vl e e' v Fs hds k,
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩) ->
  | FApp2 (VFun vl e) hds (map VVal hds' ++ e' :: vals) :: Fs, v | k ↓ ->
  exists k0 hds'', k0 <= k /\
  ⟨ FApp2 (VFun vl e) hds (hds' ++ e' :: vals) :: Fs, v ⟩ -[k0]-> 
  ⟨ FApp2 (VFun vl e) (hds ++ v :: hds'') vals :: Fs , e'⟩.
Proof.
  induction hds'; intros.
  * simpl in *. inversion H0; subst; try inversion_is_value.
    exists 1, []. split. lia. split. auto. econstructor. constructor; auto. constructor.
  * simpl in *. inversion H0; subst; try inversion_is_value.
    apply H in H12 as P1. 2: lia. destruct P1, H3, H3.
    eapply (terminates_step_any_2 _ _ _ _ H12) in H4 as H4'.
    inversion H4'; subst; try inversion_is_value.
    2: { destruct hds'; inversion H7. }
    destruct hds'; simpl in H6; inversion H6; subst.
    - simpl in H4.
      assert (⟨ FApp2 (VFun vl e) (e' :: vals) (hds ++ [v]) :: Fs, x ⟩ -[1]->
           ⟨ FApp2 (VFun vl e) vals ((hds ++ [v]) ++ [x]) :: Fs, e' ⟩).
           { do 2 econstructor; auto. }
      epose proof (transitive_eval _ _ _ _ _ H4 _ _ _ H5).
      exists (S (x0 + 1)), [x]. split. lia. split. auto.
      econstructor. constructor; auto.
      rewrite <- app_assoc in H7. simpl in H7. auto.
    - epose proof (IHhds' vals vl e e' x Fs _ _ _ _ _ H4' H'0 H15).
      Unshelve. 4: { intros. eapply H. 3: exact H8. lia. auto. }
      destruct H5, H5, H5, H7.
      epose proof (transitive_eval _ _ _ _ _ H4 _ _ _ H8).
      exists (S (x0 + x1)), (x::x2). 
      split. 2: split.
      + lia.
      + constructor; auto.
      + econstructor. constructor; auto. simpl in H9.
        replace ((hds ++ [v]) ++ x :: x2) with (hds ++ v :: x :: x2) in H9.
        exact H9.
        rewrite <- app_assoc. auto.
      + auto.
      + now inversion PP.
    - now inversion PP.
Qed. *)

Lemma eval_app_partial_core_emtpy :
  forall hds' vals vfun e' (v : Val) Fs (hds : list Val) k ,
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ 
    -> exists (v : Val) (k : nat),  ⟨ [], e ⟩ -[ k ]-> ⟨ [], v ⟩) ->
  | FApp2 vfun hds (hds' ++ e' :: vals) :: Fs, v | k ↓ ->
  exists k0 hds'', k0 <= k /\
  ⟨ [FApp2 vfun hds (hds' ++ e' :: vals)], v ⟩ -[k0]-> 
  ⟨ [FApp2 vfun (hds ++ v :: hds'') vals] , e'⟩.
Proof.
  induction hds'; intros.
  * simpl in *. inv H0.
    exists 1, []. split. lia. econstructor. constructor; auto. constructor.
  * simpl in *. inv H0.
    apply H in H8 as P1. 2: lia. destruct P1 as [v1 [k1 D1]].
    eapply frame_indep_nil in D1 as D1_1.
    eapply (terminates_step_any_2 _ _ _ _ H8) in D1_1 as H4'.
    inversion H4'.
    2: { destruct hds'; inversion H3. }
    destruct hds'; simpl in H3; inv H3; subst.
    - simpl in H1.
      assert (⟨ [FApp2 vfun (hds ++ [v]) (e' :: vals)], v1 ⟩ -[1]->
           ⟨ [FApp2 vfun ((hds ++ [v]) ++ [v1]) vals], e' ⟩).
      { do 2 econstructor; auto. }
      eapply frame_indep_nil in D1.
      epose proof (transitive_eval _ _ _ _ _ D1 _ _ _ H0).
      exists (S (k1 + 1)), [v1]. split. lia.
      econstructor. constructor; auto.
      rewrite <- app_assoc in H2. simpl in H2. auto.
    - epose proof (IHhds' vals vfun e' _ Fs _ _ _ H4') as X.
      Unshelve. 2: { intros. eapply H. 2: exact H2. lia. }
      destruct X as [k2 [vs2 [Hlt HD]]].
      eapply frame_indep_nil in D1.
      epose proof (transitive_eval _ _ _ _ _ D1 _ _ _ HD).
      exists (S (k1 + k2)), (v1::vs2). 
      split.
      + lia.
      + econstructor. constructor; auto. simpl in H0.
        rewrite <- app_assoc in H0.
        exact H0.
Qed.

Lemma term_bif_eval_empty :
  forall tl Fs v0 vals lst (hd : Val) k,
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    | Fs, e | m ↓ ->
    exists (v : Val) (k : nat),
      ⟨ [], e ⟩ -[ k ]-> ⟨ [], v ⟩) ->
  | FBIF2 v0 vals (tl ++ [lst]) :: Fs, hd | k ↓ ->
  exists i vals', i <= k /\
    ⟨ FBIF2 v0 vals (tl ++ [lst]) :: [], hd ⟩ -[i]->
    ⟨ FBIF2 v0 (vals ++ [hd] ++ vals') [] :: [], lst ⟩.
Proof.
  induction tl; intros; simpl.
  * inv H0.
    exists 1, []. split.
    lia.
    econstructor. constructor; auto. constructor.
  * inv H0.
    apply H in H8 as HH; auto. destruct HH as [v1 [k1 HH]].
    eapply frame_indep_nil in HH as HH0.
    eapply (terminates_step_any_2 _ _ _ _ H8) in HH0 as HH'; auto.
    destruct (k0 - k1) eqn:Eq. inversion HH'.
    epose proof (IHtl Fs v0 (vals ++ [hd]) lst v1 (S n) _ HH') as X.
    destruct X as [k2 [vals' [Hlt X]]].
    exists (S (k1 + k2)), (v1 :: vals').
    split. lia.
    econstructor. constructor; auto.
    eapply transitive_eval.
    eapply frame_indep_nil in HH. exact HH.
    simpl in X.
    rewrite <- app_assoc in X. exact X.
  Unshelve.
    intros. eapply H. 2: exact H1. lia.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
Theorem term_eval_empty : forall x Fs e, | Fs, e | x ↓ ->
  exists (v : Val) k, ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ /\ k <= x.
Proof.
  induction x using lt_wf_ind. destruct x; intros; inversion H0; subst; try congruence.
  * exists v, 0. now repeat constructor.
  * exists v, 0. split; [ do 2 constructor | lia ].
  * exists v, 0. split; [ now constructor | lia ].
  * exists v, 0. split; [ now constructor | lia ].
  * exists v, 0. split; [ now constructor | lia ].
  * exists v, 0. split; [ now constructor | lia ].
  * eexists. exists 0. split; [ now constructor | lia ].
  * exists v', 0. split; [ now constructor | lia ].
  * exists v', 0. split; [ now constructor | lia ].
  * eexists. exists 0. split; [ now constructor | lia ].
  * exists v, 0. split; [ now constructor | lia ].
  * exists v2, 0. split; [ now constructor | lia ].
  * exists v1, 0. split; [ now constructor | lia ].
  * apply H in H4 as HH. 2: lia. destruct HH as [v0 [k0 [HD0 Hlt0]]].
    eapply frame_indep_nil in HD0 as H2_1.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2_1 as H2'.
    inversion H2'; subst.
    - apply H in H9. 2: lia. destruct H9 as [v1 [k1 [HD1 Hlt1]]].
      exists v1, (S (k0 + S k1)). split. 2: lia.
      econstructor. constructor. eapply transitive_eval; eauto.
      eapply frame_indep_nil in HD0. exact HD0.
      econstructor. constructor. all: eauto.
    - apply H in H9. 2: lia. destruct H9 as [v1 [k1 [HD1 Hlt1]]].
      exists v1, (S (k0 + S k1)). split. 2: lia.
      econstructor. constructor. eapply transitive_eval; eauto.
      eapply frame_indep_nil in HD0. exact HD0.
      econstructor. apply red_case_false. all: eauto.
  * apply H in H4 as v_eval. 2: lia. destruct v_eval, H1, H1.
    eapply frame_indep_nil in H2 as H2_1.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2_1 as H2'.
    destruct vs.
    - inversion H2'; subst; try inversion_is_value.
      apply H in H7. 2: lia. destruct H7, H3, H3.
      exists x0, (S (x1 + S x2)). split; auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      eapply frame_indep_nil in H2. exact H2.
      econstructor. constructor. auto.
      inversion H1. apply -> subst_preserves_scope_exp; eauto.
    - inversion H2'; subst; try inversion_is_value.
      assert (| FApp2 x0 vs [] :: Fs, e | k ↓) as PP by auto.
      eapply H in H10. 2: lia. destruct H10, H3, H3.
      destruct (length vs) eqn:P0.
      + apply length_zero_iff_nil in P0. subst.
        eapply frame_indep_nil in H5 as H5_1.
        eapply (terminates_step_any_2 _ _ _ _ PP) in H5_1 as H5'.
        inversion H5'; subst; try inversion_is_value.
        apply H in H16. 2: lia. destruct H16, H6, H6.
        assert (⟨ [FApp2 (VFun vl e1) [] []], x2 ⟩ -[1]-> ⟨ [], e1.[list_subst (VFun vl e1 :: [] ++ [x2]) idsubst] ⟩).
        { repeat econstructor; auto. }
        eapply frame_indep_nil in H7.
        epose proof (transitive_eval _ _ _ _ _ H10 _ _ _ H7).
        assert (⟨ [FApp1 [e]], VFun vl e1 ⟩ -[1]-> ⟨ [FApp2 (VFun vl e1) [] []], e ⟩). { do 2 econstructor; auto. }
        eapply frame_indep_nil in H2.
        epose proof (transitive_eval _ _ _ _ _ H2 _ _ _ H16).
        eapply frame_indep_nil in H5.
        epose proof (transitive_eval _ _ _ _ _ H5 _ _ _ H10).
        epose proof (transitive_eval _ _ _ _ _ H17 _ _ _ H18).
        epose proof (transitive_eval _ _ _ _ _ H19 _ _ _ H7).
        exists x0, (S (x1 + 1 + (x3 + 1) + x4)). split; auto.
        econstructor. constructor. auto.
        inversion H1.
        apply -> subst_preserves_scope_exp; eauto; subst.
        simpl. apply cons_scope; auto. rewrite H14. apply cons_scope; auto.
      + apply eq_sym, last_element_exists in P0. destruct P0, H6. subst.
        eapply frame_indep_nil in H5 as H5_1.
        eapply (terminates_step_any_2 _ _ _ _ PP) in H5_1 as H5'.

        epose proof (eval_app_partial_core_emtpy x4 [] x0 x5 _ _ _ _ _ _ _ H5' H3 ltac:(auto)).
        destruct H6, H6, H6, H7. simpl in H10.
        eapply frame_indep_core in H10 as H10_1. simpl in H10_1.
        eapply (terminates_step_any_2 _ _ _ _ H5') in H10_1 as H7'.
        apply H in H7' as H7''. 2: lia. destruct H7'', H11, H11.
        eapply frame_indep_nil in H12 as H12_1.
        eapply (terminates_step_any_2 _ _ _ _ H7') in H12_1 as H11'.
        inversion H11'; subst; try inversion_is_value.
        apply H in H21. 2: lia. destruct H21, H13, H13.
        eapply frame_indep_nil in H12.
        epose proof (transitive_eval _ _ _ _ _ H10 _ _ _ H12).
        assert (⟨ [FApp2 (VFun vl e1) [] (x2 :: x7)], x8 ⟩ -[1]->
              ⟨ [], e1.[list_subst (VFun vl e1 :: (x2 :: x7) ++ [x8]) idsubst] ⟩). { econstructor. constructor; auto. constructor. }
        epose proof (transitive_eval _ _ _ _ _ H15 _ _ _ H18).
        epose proof (transitive_eval _ _ _ _ _ H21 _ _ _ H14).
        eapply frame_indep_nil in H5.
        epose proof (transitive_eval _ _ _ _ _ H5 _ _ _ H22).
        assert (⟨ [FApp1 (e :: x4 ++ [x5])], VFun vl e1 ⟩ -[1]->
            ⟨ [FApp2 (VFun vl e1) (x4 ++ [x5]) []] , e ⟩).
            { econstructor. constructor. auto. constructor. }
        simpl app in *.
        epose proof (transitive_eval _ _ _ _ _ H24 _ _ _ H23).
        eapply frame_indep_nil in H2.
        epose proof (transitive_eval _ _ _ _ _ H2 _ _ _ H25).

        exists x0, (S (x1 + (1 + (x3 + (x6 + x9 + 1 + x10))))). split; auto.
        econstructor. constructor. auto.
     Unshelve.
       ** inversion H1. subst. apply -> subst_preserves_scope_exp; eauto.
          replace (S (Datatypes.length vl) + 0) with (length ((VFun vl e1 :: (x2 :: x7) ++ [x8]))). 2: { simpl. rewrite app_length. simpl in *. lia. }
          apply scoped_list_idsubst. simpl. do 2 constructor; auto.
          apply Forall_app; auto.
        ** inversion P. 2: inversion_is_value.
           subst. rewrite <- indexed_to_forall in H14.
           inversion H14. subst. rewrite Forall_app in H16; auto.
           destruct H16. now inversion H12.
        ** inversion P. 2: inversion_is_value.
           rewrite <- indexed_to_forall in H11. now inversion H11.
        ** inversion P. 2: inversion_is_value.
           rewrite <- indexed_to_forall in H11. inversion H11.
           now rewrite Forall_app in H15.
        ** intros. eapply H. 3: exact H10. lia. auto.
      + inversion P. 2: inversion_is_value. apply (H7 0); simpl; lia.
    - now inversion P.
  * inversion P; subst. 2: inversion_is_value.
    apply H in H4 as HH; auto. destruct HH as [v0 [k0 [v0CL HH]]].
    eapply frame_indep_nil in HH as HH0.
    eapply (terminates_step_any_2 _ _ _ _ H4) in HH0 as HH'.
    inversion HH'; subst; try inversion_is_value; auto.
    destruct (length tl) eqn:Len.
    - apply length_zero_iff_nil in Len. subst.
      apply H in H9 as H9'; auto. 2: lia.
      destruct H9' as [hd' [k1 [hd'Vcl H9']]].
      eapply frame_indep_nil in H9' as H9'0.
      eapply (terminates_step_any_2 _ _ _ _ H9) in H9'0 as H9''.
      inversion H9''; subst; try inversion_is_value.
      inversion P; subst. apply (H10 0 ltac:(simpl;lia)).
      inversion_is_value.
    - apply eq_sym, last_element_exists in Len as [tl' [lst ?]]; subst.
      inversion P; subst; try inversion_is_value.
      apply indexed_to_forall in H10.
      inversion H10. subst. apply Forall_app in H12 as [H12_1 H12_2].
      inversion H12_2; subst.
      apply H in H9 as H9'; auto. 2: lia.
      destruct H9' as [hd' [k1 [hd'Vcl H9']]].
      eapply frame_indep_nil in H9' as H9'0.
      eapply (terminates_step_any_2 _ _ _ _ H9) in H9'0 as H9''.
      epose proof (term_bif_eval_empty tl' Fs v0 [] lst hd' _ _ H9'' _ _ _).
      destruct H1 as [k2 [vals' [Hlt [Hall Der]]]].
      eapply frame_indep_core in Der as Der0.
      eapply (terminates_step_any_2 _ _ _ _ H9'') in Der0 as Der'.
      eapply H in Der' as Der''; auto. 2: lia.
      destruct Der'' as [lstval [k3 [VCl3 Der'']]].
      eapply frame_indep_nil in Der'' as Der''0.
      epose proof (transitive_eval _ _ _ _ _ Der _ _ _ Der''0) as DEND.
      simpl app in *.
      eapply frame_indep_nil in H9'.
      epose proof (transitive_eval _ _ _ _ _ H9' _ _ _ DEND) as COMP.
      assert (⟨ FBIF1 (hd :: tl' ++ [lst]) :: [], v0 ⟩ -[1]->
              ⟨ FBIF2 v0 (tl' ++ [lst]) [] :: [], hd ⟩) as ONE. {
        econstructor. constructor. auto. constructor.
      }
      epose proof (transitive_eval _ _ _ _ _ ONE _ _ _ COMP) as COMP'.
      eapply frame_indep_nil in HH.
      epose proof (transitive_eval _ _ _ _ _ HH _ _ _ COMP') as COMP''.
      simpl in COMP''.
      eapply frame_indep_nil in Der''.
      eapply (terminates_step_any_2 _ _ _ _ Der') in Der'' as Der'''.
      inversion Der'''; subst; try inversion_is_value.
      exists (VLit (i1 + i2)%Z). eexists.
      split; auto.
      econstructor. constructor.
      eapply transitive_eval. exact COMP''.
      econstructor. constructor. constructor.
    Unshelve.
      all: auto.
      intros. eapply H. 3: exact H14. lia. auto.
  * apply H in H4 as HH. destruct HH, H1, H1. 2: lia.
    eapply frame_indep_nil in H2 as H2_1.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2_1 as H2'.
    inversion H2'; subst; try inversion_is_value.
    apply H in H10 as HH. destruct HH, H3, H3. 2: lia.
    eapply frame_indep_nil in H5 as H5_1.
    eapply (terminates_step_any_2 _ _ _ _ H10) in H5_1 as H5'.
    exists x2, (S (x1 + (S x3))).
    split. auto.
    econstructor. constructor. eapply transitive_eval; eauto.
    eapply frame_indep_nil in H2. exact H2. 
    econstructor. constructor; auto. auto.

    inversion P. 2: inversion_is_value. 
    apply -> subst_preserves_scope_exp; eauto.
    now inversion P.
  * apply H in H4 as HH. 2: lia. 2: now inversion P.
    destruct HH as [v2 [k2 [V2CL Eval2]]].
    eapply frame_indep_nil in Eval2 as Eval2'.
    eapply (terminates_step_any_2 _ _ _ _ H4) in Eval2'.
    inversion Eval2'; subst; try inversion_is_value.
    apply H in H7 as [v1 [k1 [V1CL Eval1]]]. 2: lia. 2: now inversion P.
    assert (⟨ [FCons1 e1], v2 ⟩ -[1]-> ⟨ [FCons2 v2], e1 ⟩).
    { econstructor. constructor. auto. constructor. }
    eapply transitive_eval in H1.
    2: eapply frame_indep_nil in Eval2 as Eval2''; exact Eval2''.
    eapply frame_indep_nil in Eval1 as Eval1''.
    eapply transitive_eval in Eval1''. 2: exact H1.
    assert (⟨ [FCons2 v2], v1 ⟩ -[1]-> ⟨ [], VCons v1 v2 ⟩).
    { econstructor. constructor; auto. constructor. }
    eapply transitive_eval in H2. 2: exact Eval1''.
    exists (VCons v1 v2), (S ((k2 + 1 + k1) + 1)). split. constructor; auto.
    econstructor. constructor; auto. exact H2.
Qed.

Corollary term_eval : forall x Fs e (P : EXPCLOSED e), | Fs, e | x ↓ ->
  exists v k, VALCLOSED v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ (* /\ k <= x *).
Proof.
  intros.
  pose proof (term_eval_empty x Fs e P H).
  destruct H0, H0, H0.
  do 2 eexists. split; eauto. eapply frame_indep_nil in H1. exact H1.
Qed.

Corollary app_term_fun_final : forall tl k hds e e' Fs,
  | FApp2 e' tl hds :: Fs, e | k ↓ -> Forall (fun v => VALCLOSED v) hds ->
  EXPCLOSED e -> Forall (fun e => EXPCLOSED e) tl
->
  exists vl b, e' = VFun vl b /\ length vl = S (length (hds ++ tl)).
Proof.
  intros. eapply app_term_fun; eauto.
  intros. eapply term_eval. eauto. eauto.
Qed.

Corollary term_eval_both : forall x Fs e (P : EXPCLOSED e), | Fs, e | x ↓ ->
  exists v k, VALCLOSED v /\ ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩.
Proof.
  intros. apply term_eval_empty in H. destruct H, H, H.
  exists x0, x1; split; [| split]; auto.
  eapply frame_indep_nil in H0; eauto. auto.
Qed.

Theorem app_term_conditions : forall l1 l2 v e x Fs (P : EXPCLOSED e) (PP : Forall (fun e => EXPCLOSED e) l1), 
  | FApp2 v l1 l2 :: Fs, e | x ↓ ->
  Forall (fun v => VALCLOSED v) l2 /\ exists vl e', v = VFun vl e'.
Proof.
  induction l1; intros.
  * apply term_eval in H as H'; auto. destruct H', H0, H0.
    eapply (terminates_step_any_2 _ _ _ _ H) in H1 as H1'.
    inversion H1'; subst; try inversion_is_value. split. auto. now do 2 eexists.
  * apply term_eval in H as H'. destruct H', H0, H0.
    eapply (terminates_step_any_2 _ _ _ _ H) in H1 as H1'.
    inversion H1'; subst; try inversion_is_value. apply IHl1 in H11.
    destruct H11, H3, H3. split; auto. subst. now do 2 eexists.
    now inversion PP.
    now inversion PP.
    congruence.
Qed.

Lemma eval_bif_partial :
  forall hds vals vfun v Fs,
  Forall (fun v => EXPCLOSED v) vals ->
  Forall (fun v => VALCLOSED v) hds ->
  VALCLOSED vfun ->
  EXPCLOSED v ->
  ⟨ Fs, EBIF vfun (hds ++ v :: vals) ⟩ -[S (S (length hds))]-> 
  ⟨ FBIF2 vfun vals hds :: Fs , v⟩.
Proof.
  intro hds.
  remember (length hds) as len. generalize dependent hds.
  induction len; intros.
  * apply eq_sym, length_zero_iff_nil in Heqlen. subst.
    simpl. econstructor. constructor; auto.
    econstructor. constructor; auto. constructor.
  * apply last_element_exists in Heqlen as L'.
    destruct L' as [hds' [lst Eq]]; subst.
    apply Forall_app in H0 as [H0_1 H0_2]. inversion H0_2; subst.
    rewrite app_length in Heqlen. simpl in Heqlen.
    specialize (IHlen hds' ltac:(lia) (v::vals) vfun lst Fs
         ltac:(constructor;auto) H0_1 H1 ltac:(constructor;auto)).
    rewrite <- app_assoc. simpl.
    replace (S (S (S len))) with (S (S len) + 1) by lia.
    eapply transitive_eval. exact IHlen.
    econstructor. constructor; auto. constructor.
Qed.

Theorem put_back : forall F e Fs (P : EXPCLOSED e) (P2 : FCLOSED F),
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓.
Proof.
  destruct F; intros; simpl.
  * inversion H. exists (S x). constructor. auto.
  * destruct H.
    apply term_eval in H as H'. destruct H', H0, H0.
    apply app_term_conditions in H as CDS. destruct CDS, H3, H3. subst.
    destruct l2.
    - simpl in *. exists (2 + x). do 2 constructor; auto.
      now inversion P2.
    - inversion H2. subst.
      epose proof (eval_app_partial_core l2 l1 x2 x3 e e0 Fs [] _ _ H6 H5).
      exists (2 + (S (Datatypes.length l2) + x)). simpl.
      do 2 constructor. now inversion P2.
      apply terminates_in_k_eq_terminates_in_k_sem in H.
      apply terminates_in_k_eq_terminates_in_k_sem. destruct H, H.
      exists x4. split; auto. rewrite <- Nat.add_succ_l.
      eapply transitive_eval. exact H3. auto.
    - auto.
    - now inversion P2.
    - auto.
  * inversion H. exists (S x). constructor. auto.
  * inversion H. exists (S x). constructor. auto.
  * inversion H. exists (S x). constructor. auto.
  * inversion H. exists (S (S x)). inversion P2. do 2 constructor; auto.
  * destruct H. exists (S x). constructor. auto.
  * destruct H. 
    apply term_eval in H as HH; auto.
    destruct HH as [? [? [? ?]]]. inversion P2; subst.
    pose proof (eval_bif_partial l2 l1 v e Fs H6 H7 H5 P).
    eexists.
    eapply term_step_term_plus. exact H2. exact H.
Unshelve.
  now inversion P2.
  auto.
Qed.

Theorem put_back_rev : forall F e Fs (P : EXPCLOSED e), FCLOSED F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  destruct F; intros; simpl.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * simpl in *. inversion H. subst. destruct H0.
    destruct l2.
    - simpl in H0. inversion H0; subst; try inversion_is_value.
      inversion H8; subst; try inversion_is_value. eexists. eauto.
    - inversion H0; subst; try inversion_is_value.
      inversion H8; subst; try inversion_is_value.
      inversion H6; subst.
      apply app_term_conditions in H11 as COND.
      2: now constructor.
      2: apply Forall_app; split; [ | constructor]; auto.
      destruct COND as [FC [vl [b ?]]]. subst.
      epose proof (eval_app_partial_core l2 l1 vl b e e0 Fs [] ltac:(auto) ltac:(auto) H7 H3).
      simpl in H1.
      eapply (terminates_step_any_2 _ _ _ _ H11) in H1 as H1'. eexists. exact H1'.
      eapply Forall_impl. 2: exact H7. intros. now constructor.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. inversion H.
    subst. inversion H5; subst; try inversion_is_value. eexists. eauto.
  * destruct H0. simpl in H0. inversion H0; subst; try inversion_is_value. eexists. eauto.
  * simpl in H0. inversion H. subst. 
    destruct H0.
    pose proof (eval_bif_partial l2 l1 v e Fs H5 H6 H4 P).
    eexists.
    eapply terminates_step_any_2. exact H0.
    exact H1.
Qed.

Theorem term_app_in_k : forall Fs vl vals e k (P : VALCLOSED (VFun vl e)),
  length vl = length vals -> Forall (fun v => VALCLOSED v) vals ->
  | Fs, e.[VFun vl e .: list_subst vals idsubst] | k ↓ ->
  | Fs, EApp (VFun vl e) vals | 2 + length vl + k ↓.
Proof.
  intros. inversion H0; try inversion_is_value; subst.
  * apply length_zero_iff_nil in H. subst.
    do 2 constructor. auto.
  * destruct (length l) eqn:D1.
    - apply length_zero_iff_nil in D1. subst. rewrite H. simpl.
      do 2 constructor; auto. now constructor.
    - apply eq_sym, last_element_exists in D1 as D1'. destruct D1' as [l' [l'x EQ]].
      subst. apply Forall_app in H3 as [H3_1 H3_2]. inversion H3_2. subst.
      epose proof (eval_app_partial_core l' [] vl e l'x x Fs []
         ltac:(constructor) _ H3_1 H2). cbn in H3.
      assert (⟨ FApp2 (VFun vl e) [] (x :: l') :: Fs, l'x ⟩ -[1]-> ⟨ Fs, e.[VFun vl e .: list_subst (x :: l' ++ [l'x]) idsubst] ⟩). { 
        econstructor; constructor. all: auto.
        simpl. simpl in H. rewrite app_length in H. simpl in H. lia.
      }
      epose proof (transitive_eval _ _ _ _ _ H3 _ _ _ H4).
      eapply term_step_term_plus in H7. 2: exact H1.
      rewrite H. simpl. rewrite app_length. simpl. do 2 constructor. auto. exact H7.
  Unshelve.
    now inversion P.
    auto.
Qed.

(** The following two theorems state general properties about the evaluation
    of map and foldr. Specifically, they explain the conditions under they
    evaluate to the same list value. *)
Theorem obj_map_on_meta_level :
  forall l' l x e f
  (VsCL : VALCLOSED l) (SCE : EXP 2 ⊢ e),
  computes x e f -> cons_to_list l = Some l' ->
  ⟨[], obj_map (VFun [x] e) l⟩ -->* list_to_cons (map f l').
Proof.
  induction l'; intros.
  * destruct l; simpl in H0; inversion H0.
    2: { destruct (cons_to_list l2); inversion H0. }
    unfold obj_map. cbn.
    eexists. auto. eexists.
    econstructor. constructor. cbn.
    econstructor. constructor.
    econstructor. constructor. {
      constructor. simpl. constructor; auto.
      cbn. do 2 constructor; auto. 2: do 2 constructor; lia.
      all: intros; destruct i; simpl; constructor; auto; simpl in *.
      2-3: destruct i; try constructor; lia. constructor. lia.
    }
    econstructor. constructor. {
      constructor. simpl. constructor; auto.
      cbn. do 2 constructor; auto. 2: do 2 constructor; lia.
      all: intros; destruct i; simpl; constructor; auto; simpl in *.
      2-3: destruct i; try constructor; lia. constructor. lia.
    } auto.
    {
      constructor. simpl. rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    }
    simpl.
    econstructor. constructor; auto. constructor; auto.
    {
      constructor. simpl. rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    }
    econstructor. simpl. constructor; auto. cbn.
    econstructor. apply red_case_false; auto.
    constructor.
  * destruct l; simpl in H0; inversion H0.
    break_match_hyp; inversion H0. subst.
    inversion VsCL. subst.
    clear H0 H2 VsCL. specialize (IHl' _ _ _ _  H5 SCE H Heqo).
    destruct IHl' as [VCL [k H']].
    unfold obj_map in H'. inversion H'; subst.
    1: { rewrite <- H3 in VCL. inversion_is_value. } clear H'.
    inversion H0; subst. clear H0. simpl in H1.
    (** eval first element (necessary before eexists): *)
    specialize (H a) as [? [kk DER]].
    (***)
    unfold obj_map. split. { simpl. constructor; auto. }

    eexists.
    econstructor. constructor. cbn.
    econstructor. constructor.
    econstructor. constructor. {
      constructor. simpl. constructor; auto.
      cbn. do 2 constructor; auto. 2: do 2 constructor; lia.
      all: intros; destruct i; simpl; constructor; auto; simpl in *.
      2-3: destruct i; try constructor; lia. constructor. lia.
    }
    econstructor. constructor. {
      constructor. simpl. constructor; auto.
      cbn. do 2 constructor; auto. 2: do 2 constructor; lia.
      all: intros; destruct i; simpl; constructor; auto; simpl in *.
      2-3: destruct i; try constructor; lia. constructor. lia.
    } auto.
    {
      constructor. simpl. rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    }
    econstructor. constructor; auto. simpl. constructor.
    {
      constructor. simpl. rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    } auto.
    econstructor. constructor; auto. simpl.
    econstructor. constructor; auto. reflexivity. simpl.
    econstructor. apply step_cons.
    repeat rewrite renaming_is_subst.
    repeat rewrite ren_up.
    repeat rewrite subst_comp.
    repeat rewrite up_comp.
    repeat rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    apply frame_indep_nil with (Fs' := [FCons1
     (EApp (VFun [x] e)
        [a.[VFun [FVar; XVar]
              (ECase (VVar 2) (PCons PVar PVar)
                 (ECons (EApp (VVar 3) [VVar 0])
                    (EApp (VFunId 2) [VVar 3; VVar 1])) VNil)/]])]) in H1. simpl in H1.
    eapply transitive_eval.
    rewrite (proj2 (scoped_ignores_sub 2) e) in H1; auto.
    exact H1.
   (** evaluate first element *)
    econstructor. constructor. { auto. }
    rewrite vclosed_ignores_sub; auto.
    apply frame_indep_nil with (Fs' := [FCons2 (list_to_cons (map f l'))])
       in DER. simpl in DER.
    eapply transitive_eval. exact DER.
    econstructor. constructor; auto. constructor.
Qed.

Theorem obj_foldr_on_meta_level :
  forall l' l x y z e f
  (VsCL : VALCLOSED l) (SCE : EXP 2 ⊢ e),
  computes x e f -> cons_to_list l = Some l' ->
  ⟨[], obj_foldr (VFun [y;z] (ECons (EApp (VFun [x] e) [VVar 1]) (VVar 2))) l VNil⟩
 -->* list_to_cons (map f l').
Proof.
  induction l'; intros.
  * assert (VALCLOSED (VFun [FVar; DVar; XVar]
             (ECase (VVar 3) (PCons PVar PVar)
                (EApp (VVar 3)
                   [VVar 0; EApp (VFunId 2) [VVar 3; VVar 4; VVar 1]])
                (VVar 2)))) as CLF1. {
      do 2 constructor; auto. constructor; simpl; auto.
      * do 2 constructor. lia.
      * intros. destruct i. 2: destruct i. do 2 constructor. 1, 3: lia.
        constructor; auto. simpl. intros.
        do 2 constructor. lia.
        simpl. intros. destruct i. 2: destruct i. 3: destruct i.
        1-3: do 2 constructor. all: lia.
      * simpl. do 2 constructor. lia.
    }
    assert (VALCLOSED (VFun [y; z] (ECons (EApp (VFun [x] e) [VVar 1]) (VVar 2)))). {
      constructor. simpl. do 2 constructor.
      * do 2 constructor. simpl. now apply (proj2 (scope_ext_app 5 2 ltac:(lia))).
      * intros. simpl in H1. destruct i. do 2 constructor. all: lia.
      * constructor. lia.
    }
    destruct l; simpl in H0; inversion H0.
    2: { destruct (cons_to_list l2); inversion H0. }
    unfold obj_map. cbn.
    eexists. auto. eexists.
    econstructor. constructor. cbn.
    econstructor. constructor.
    econstructor. constructor. auto.
    repeat rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    econstructor. constructor; auto.
    cbn.
    econstructor. constructor; auto.
    econstructor. constructor; auto.
    {
      constructor. auto.
      constructor; auto.
    } cbn.
    econstructor. constructor; auto.
    econstructor. apply red_case_false; auto.
    constructor.
  * destruct l; simpl in H0; inversion H0.
    break_match_hyp; inversion H0. subst.
    inversion VsCL. subst.
    clear H0 H2 VsCL. specialize (IHl' _ _ y z _ _ H5 SCE H Heqo).
    destruct IHl' as [VCL [k H']].
    unfold obj_foldr in H'. inversion H'; subst.
    1: { rewrite <- H3 in VCL. inversion_is_value. } clear H'.
    inversion H0; subst. clear H0. simpl in H1.
    (** eval first element (necessary before eexists): *)
    specialize (H a) as [? [kk DER]].
    (***)
    unfold obj_map. split. { simpl. constructor; auto. }
    assert (VALCLOSED (VFun [FVar; DVar; XVar]
             (ECase (VVar 3) (PCons PVar PVar)
                (EApp (VVar 3)
                   [VVar 0; EApp (VFunId 2) [VVar 3; VVar 4; VVar 1]])
                (VVar 2)))) as CLF1. {
      do 2 constructor; auto. constructor; simpl; auto.
      * do 2 constructor. lia.
      * intros. destruct i. 2: destruct i. do 2 constructor. 1, 3: lia.
        constructor; auto. simpl. intros.
        do 2 constructor. lia.
        simpl. intros. destruct i. 2: destruct i. 3: destruct i.
        1-3: do 2 constructor. all: lia.
      * simpl. do 2 constructor. lia.
    }
    assert (VALCLOSED (VFun [y; z] (ECons (EApp (VFun [x] e) [VVar 1]) (VVar 2)))) as CLVF2. {
      constructor. simpl. do 2 constructor.
      * do 2 constructor. simpl. now apply (proj2 (scope_ext_app 5 2 ltac:(lia))).
      * intros. simpl in H1. destruct i. do 2 constructor. lia.
        simpl in *. lia.
      * constructor. lia.
    }
    eexists.
    econstructor. constructor. cbn.
    econstructor. constructor.
    econstructor. constructor. auto.
    repeat rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    rewrite (proj2 (scoped_ignores_sub 2) e) in H1; auto.
    econstructor. constructor; auto. simpl.
    econstructor. constructor; auto.
    econstructor. constructor; auto.
    {
      constructor. auto.
      constructor; auto.
    } simpl.
    econstructor. constructor; auto.
    econstructor. constructor; auto. reflexivity. simpl.
    repeat rewrite renaming_is_subst.
    repeat rewrite ren_up.
    repeat rewrite subst_comp.
    repeat rewrite up_comp.
    repeat rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    repeat rewrite vclosed_ignores_sub; auto.
    rewrite vclosed_ignores_sub in H1; auto.
    econstructor. constructor.
    econstructor. constructor. auto.
    econstructor. constructor; auto. simpl.
    apply frame_indep_nil with (Fs' :=  [FApp2 (VFun [y; z] (ECons (EApp (VFun [x] e) [VVar 1]) (VVar 2))) [] [a]]) in H1. simpl in H1.
    eapply transitive_eval. exact H1.
   (** evaluate first element *)
    econstructor. constructor; auto. simpl.
    repeat rewrite (proj2 (scoped_ignores_sub 2) e); auto.
    econstructor. constructor.
    econstructor. constructor. { auto. }
    apply frame_indep_nil with (Fs' := [FCons2 (list_to_cons (map f l'))])
       in DER. simpl in DER.
    eapply transitive_eval. exact DER.
    econstructor. constructor; auto. constructor.
Qed.
