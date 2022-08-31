Require Export Scoping.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Export Coq.Arith.Wf_nat.
Export PeanoNat.

Import ListNotations.

(** Based on https://github.com/cobbal/ppl-ctx-equiv-coq 
    Frame stack semantics:
*)


Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_app_start v hd tl xs (H : VALCLOSED v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v tl [])::xs, hd⟩

| red_app_fin xs e :
  ⟨ (FApp1 [])::xs, EFun [] e ⟩ --> ⟨ xs, e.[EFun [] e/] ⟩

| app2_step v (H : VALCLOSED v) hd tl vs (H2 : Forall (fun v => VALCLOSED v) vs) xs v' (H' : VALCLOSED v') :
  ⟨ (FApp2 v (hd::tl) vs) :: xs, v' ⟩ --> ⟨ (FApp2 v tl (vs ++ [v'])) :: xs, hd ⟩

| red_app2 vl e vs v xs (H2 : Forall (fun v => VALCLOSED v) vs) : 
  VALCLOSED v -> length vl = S (length vs) ->
  ⟨ (FApp2 (EFun vl e) [] vs) :: xs, v ⟩ --> ⟨ xs,  e.[list_subst (EFun vl e :: (vs ++ [v])) idsubst] ⟩

| red_bif_start fs e params v : VALCLOSED v ->
  ⟨FBIF1 (e::params) :: fs, v⟩ --> ⟨ FBIF2 v params [] ::fs , e⟩
| red_bif_step fs e v v' params vals :
  Forall (fun v => VALCLOSED v) vals -> VALCLOSED v -> VALCLOSED v' ->
  ⟨FBIF2 v (e :: params) vals :: fs, v'⟩ -->
  ⟨FBIF2 v params (vals ++ [v']) :: fs, e⟩

| red_let val e2 xs v (H : VALCLOSED val) : ⟨ (FLet v e2)::xs, val ⟩ --> ⟨ xs, e2.[val/] ⟩

| red_case_true e2 e3 v p xs l : 
  VALCLOSED v -> match_pattern p v = Some l
->
  ⟨ (FCase p e2 e3)::xs, v ⟩ --> ⟨ xs, e2.[list_subst l idsubst] ⟩

| red_case_false e2 e3 p v xs (H : VALCLOSED v) :
  VALCLOSED v -> match_pattern p v = None ->
  ⟨ (FCase p e2 e3)::xs, v ⟩ --> ⟨ xs, e3 ⟩

| red_letrec xs f vl b e:
  ⟨ xs, ELetRec f vl b e ⟩ --> ⟨ xs, e.[EFun vl b/] ⟩

| red_cons1 xs v2 e1 (H : VALCLOSED v2):
  ⟨ FCons1 e1::xs, v2⟩ --> ⟨FCons2 v2::xs, e1 ⟩

| red_cons2 xs v2 v1 (H : VALCLOSED v1) (H0 : VALCLOSED v2):
  ⟨ FCons2 v2::xs, v1⟩ --> ⟨xs, VCons v1 v2 ⟩

| red_plus xs i1 i2 :
  ⟨ (FBIF2 (ELit "+"%string) [] [ELit (Int i1)]) :: xs, ELit (Int i2)⟩ --> 
    ⟨xs, ELit (Z.add i1 i2)⟩

(** Steps *)
| step_let xs v e1 e2 : ⟨ xs, ELet v e1 e2 ⟩ --> ⟨ (FLet v e2)::xs, e1 ⟩
| step_app xs e el: ⟨ xs, EApp e el ⟩ --> ⟨ (FApp1 el)::xs, e ⟩
| step_bif fs name params:
  ⟨fs, EBIF name params⟩ --> ⟨FBIF1 params :: fs, name⟩
| step_case xs e1 p e2 e3 : ⟨ xs, ECase e1 p e2 e3⟩ --> ⟨ (FCase p e2 e3)::xs, e1⟩

(** Special step rules: need to "determinize them" *)
| step_cons xs e1 e2: ⟨ xs, ECons e1 e2 ⟩ --> ⟨ (FCons1 e1) :: xs, e2 ⟩
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Exp -> nat -> FrameStack -> Exp -> Prop :=
| step_refl e Fs : ⟨ Fs, e ⟩ -[ 0 ]-> ⟨ Fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').

Definition step_any (fs : FrameStack) (e : Exp) (v : Exp) : Prop :=
  VALCLOSED v /\ exists k, ⟨fs, e⟩ -[k]-> ⟨[], v⟩.

Notation "⟨ fs , e ⟩ -->* v" := (step_any fs e v) (at level 50).

Global Hint Constructors ExpScoped : core.
Global Hint Constructors ValScoped : core.

Open Scope Z_scope.
Goal ⟨ [], inc 1 ⟩ -->* ELit 2.
Proof.
  repeat (econstructor;cbn).
Qed.

Local Goal ⟨ [], simplefun 10 ⟩ -->* ELit 10.
Proof.
  repeat econstructor.
Qed.

Local Goal ⟨ [], simplefun2 10 10 ⟩ -->* ELit 20.
Proof.
  unfold simplefun2.
  repeat econstructor.
  all: inversion H; subst; cbn in *; auto.
  all: inversion H1; subst; cbn in *; auto; lia.
Qed.

Local Goal ⟨ [], sum 1 ⟩ -->* ELit 1%Z.
Proof.
  assert (VALCLOSED (EFun [XVar]
             (ECase (EVar 1) (PLit 0) (EVar 1)
                (EBIF (ELit "+"%string) [EVar 1; EApp (EFunId 0) [EBIF (ELit "+"%string) [EVar 1; ELit (-1)]]])))). {
    do 3 constructor; auto.
    intros. inversion H; subst; cbn. 2: inversion H1.
    all: auto.
    constructor; auto.
    intros. inversion H0. 2: inversion H2.
    constructor; auto.
    intros. inversion H1. 2: inversion H4. 3: inversion H6.
    all: cbn; auto.
    lia.
  }
  unfold sum.
  simpl.
  constructor. constructor. econstructor.
  econstructor.
  econstructor.
  econstructor. constructor. cbn. econstructor. constructor. auto.
  econstructor.
  eapply red_app2. constructor.
  simpl. econstructor. econstructor. econstructor. cbn. eapply step_case.
  econstructor. eapply red_case_false. constructor. constructor. cbn. congruence.
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
  simpl. econstructor. econstructor. econstructor. cbn. eapply step_case.
  econstructor. eapply red_case_true. constructor. reflexivity.
  econstructor. eapply red_plus.
  econstructor.
Qed.

Local Goal ⟨[], ECons (EBIF (ELit "+"%string) [ELit 1; ELit 1]) (ECons (ELit 1) (ECons (ELit 0) ENil))⟩ -->* VCons (ELit 2) (VCons (ELit 1) (VCons (ELit 0) ENil)).
Proof.
  split. repeat constructor. exists 13%nat.
  econstructor. constructor.
  econstructor. apply step_cons.
  econstructor. apply step_cons. econstructor. constructor. constructor.
  econstructor. constructor; constructor.
  econstructor. constructor. repeat constructor.
  econstructor. constructor; repeat constructor.
  econstructor. constructor. repeat constructor.
  econstructor. apply step_bif.
  econstructor. constructor. constructor.
  econstructor. constructor.
  econstructor. constructor. 1-2: repeat constructor.
  repeat econstructor.
Qed.

Local Goal
   ⟨[], obj_map (EFun [YVar] (EBIF (ELit "+"%string) [EVar 1; ELit 1]))
                (ECons (ELit 0) (ECons (ELit 1) (ECons (ELit 2) ENil)))⟩ -->*
   VCons (ELit 1) (VCons (ELit 2) (VCons (ELit 3) ENil)).
Proof.
  split; auto. exists 60%nat.
  econstructor. constructor. simpl.
  econstructor. constructor. simpl.
  econstructor. constructor. { constructor. cbn. repeat constructor.
                               all: destruct i.
                               all: try destruct i. all: simpl in H; try lia.
                               all: simpl; auto; constructor; lia. }
  do 10 (econstructor; auto).
  (** first element *)
  constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto. reflexivity. cbn.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. { constructor. cbn. repeat constructor.
                               all: destruct i.
                               all: try destruct i. all: simpl in H; try lia.
                               all: simpl; auto; constructor; lia. }
  (** second element *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto. reflexivity. cbn.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. { constructor. cbn. repeat constructor.
                               all: destruct i.
                               all: try destruct i. all: simpl in H; try lia.
                               all: simpl; auto; constructor; lia. }
  (** third element *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. constructor; auto. reflexivity. cbn.
  econstructor. apply step_cons. auto. cbn.
  econstructor. apply step_app.
  econstructor. constructor. { constructor. cbn. repeat constructor.
                               all: destruct i.
                               all: try destruct i. all: simpl in H; try lia.
                               all: simpl; auto; constructor; lia. }
  (** end *)
  econstructor. constructor; auto. cbn.
  econstructor. apply step_case; auto.
  econstructor. apply red_case_false; auto.
  (** apply function to list elements *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto. { constructor. cbn. repeat constructor.
                                     destruct i.
                                     2: try destruct i. all: simpl in *;
                                        try lia; constructor; lia. }
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.
  (** apply function to list elements *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto. { constructor. cbn. repeat constructor.
                                     destruct i.
                                     2: try destruct i. all: simpl in *;
                                        try lia; constructor; lia. }
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.
  (** apply function to list elements *)
  econstructor. constructor; auto.
  econstructor. apply step_app; auto.
  econstructor. constructor; auto. { constructor. cbn. repeat constructor.
                                     destruct i.
                                     2: try destruct i. all: simpl in *;
                                        try lia; constructor; lia. }
  econstructor. constructor; auto. cbn.
  econstructor. apply step_bif; auto.
  econstructor. constructor; auto.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto. cbn.
  econstructor. constructor; auto.
  constructor.
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
  intro H. dependent induction H; intros.
  * inversion H0; subst; try inversion H; try (proof_irr; auto).
  * inversion H; subst. auto.
  * inversion H0; subst; try inversion H'; try (proof_irr_many; auto).
  * inversion H1; subst; try inversion H; auto.
  * inversion H0; subst; try inversion H'; try (proof_irr_many; auto); try inversion_is_value.
  * inversion H2; subst; try inversion_is_value; auto.
  * inversion H0; subst; auto; try inversion H.
  * inversion H1; subst; auto; try inversion_is_value.
    rewrite H0 in H10. inversion H10. auto. congruence.
  * inversion H2; subst; auto; try inversion_is_value. congruence.

  * inversion H; subst; try inversion_is_value; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H0; subst; try inversion_is_value. auto.
  * inversion H1; subst; try inversion_is_value; auto.
  * inversion H; subst; try inversion_is_value; try inversion H'; try inversion H1; try (proof_irr_many; auto).
  * inversion H; subst; try congruence; try inversion_is_value; auto.
  * inversion H; subst; try congruence; try inversion_is_value; auto.
  * inversion H; subst; try congruence; try inversion_is_value; auto.
  * inversion H; subst; try congruence; try inversion_is_value; auto.
  * inversion H; subst; try congruence; try inversion_is_value; auto.
Qed.

Theorem value_nostep v (H : VALCLOSED v) :
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  dependent induction H; intros.
  * inversion H.
  * inversion H.
  * inversion H1.
  * inversion H.
  * inversion H.
  * inversion H.
  * inversion H0.
Qed.

Theorem step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩ -> VALCLOSED v
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
  intros F e F' e' IH. induction IH; intros; try inversion_is_value.
  * inversion H0. subst. inversion H4. inversion H3. subst. split; auto.
    constructor; auto. constructor; auto.
  * inversion H. inversion H0. subst. split; auto. inversion H5. subst. cbn in H2.
    apply -> subst_preserves_scope_exp; eauto.
  * inversion H0. subst. inversion H5. inversion H9. subst. split; auto. constructor; auto.
    constructor; auto.
    apply Forall_app. split; auto.
  * inversion H1. inversion H6. split. auto. subst. inversion H11.
    apply -> subst_preserves_scope_exp; eauto. subst.
    rewrite Nat.add_0_r. replace (S (length vl)) with (length (EFun vl e :: vs ++ [v])).
    apply scoped_list_idsubst. constructor. auto. apply Forall_app. split; auto.
    simpl. rewrite H0, app_length. simpl. lia.
  * inversion H0. subst. inversion H4. inversion H3. subst. split; auto.
    constructor; auto. constructor; auto.
  * inversion H2. inversion H6. inversion H12.
    subst. split; auto.
    constructor; auto. constructor; auto.
    apply Forall_app. split; auto.
  * inversion H0. inversion H4. 
    subst. split; auto. apply -> subst_preserves_scope_exp; eauto.
  * inversion H1. inversion H5. subst. split; auto.
    apply -> subst_preserves_scope_exp; eauto.
    rewrite (match_pattern_length _ v l H0).
    apply scoped_list_idsubst. eapply match_pattern_scoped; eauto.
  * inversion H2. inversion H6. subst. split; auto.
  * split; auto. inversion H0. 2: inversion H1. apply -> subst_preserves_scope_exp; eauto.
  * inversion H0. inversion H4. subst. split; auto. repeat constructor; auto.
  * inversion H1. inversion H5. subst. split; auto.
  * inversion H; subst. split; auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    now constructor.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite Nat.add_0_r in H6. auto. auto.
  * inversion H0; subst; split; auto. 1-2: constructor; auto; now constructor.
    now inversion H1.
Qed.

Theorem result_VALCLOSED_any (fs : FrameStack) (e v : Exp) :
  ⟨ fs, e ⟩ -->* v -> VALCLOSED v.
Proof.
  intros. destruct H. auto.
Qed.

Corollary step_any_closedness : forall F e v,
   ⟨ F, e ⟩ -->* v -> FSCLOSED F -> EXPCLOSED e
->
  VALCLOSED v.
Proof.
  intros. destruct H, H2. induction H2.
  * destruct e; try inversion H; now inversion H1.
  * apply step_closedness in H2; auto.
Qed.

Definition terminates_sem (fs : FrameStack) (e : Exp) : Prop :=
  exists v, ⟨fs, e⟩ -->* v.

Definition terminates_in_k_sem (fs : FrameStack) (e : Exp) (k : nat) : Prop :=
  exists v, ⟨fs, e⟩ -[k]-> ⟨[], v⟩ /\ VALCLOSED v.

Open Scope nat_scope.

Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Exp -> nat -> Prop :=

| term_value v : VALCLOSED v -> | [] , v | 0 ↓
| term_case_true fs e1 e2 k v p l :
  VALCLOSED v ->  match_pattern p v = Some l -> | fs , e1.[list_subst l idsubst] | k ↓
 ->
  | (FCase p e1 e2)::fs , v | S k ↓
| term_case_false fs e1 e2 v k p :
  VALCLOSED v ->  match_pattern p v = None -> | fs , e2 | k ↓ 
 -> 
  | (FCase p e1 e2)::fs , v | S k ↓
| term_let_subst v e2 fs k x : VALCLOSED v -> | fs, e2.[v/] | k ↓ -> | (FLet x e2)::fs, v | S k ↓
| term_letrec_subst vl b e fs f k : | fs, e.[EFun vl b/] | k ↓ -> | fs, ELetRec f vl b e | S k ↓
| term_app_start v hd tl (H : VALCLOSED v) fs k : 
  | (FApp2 v tl [])::fs, hd| k ↓ -> | (FApp1 (hd::tl))::fs, v | S k ↓
| term_bif_start v hd tl (H : VALCLOSED v) fs k : 
  | (FBIF2 v tl [])::fs, hd| k ↓ -> | (FBIF1 (hd::tl))::fs, v | S k ↓
| term_app1 e fs k : | fs, e.[EFun [] e/] | k ↓ -> | (FApp1 [])::fs, EFun [] e | S k ↓
| term_app_step v v' (H : VALCLOSED v) hd tl vs (H2 : Forall (fun v => VALCLOSED v) vs) (H' : VALCLOSED v') fs k :
  | (FApp2 v tl (vs ++ [v']))::fs, hd | k ↓ -> | (FApp2 v (hd::tl) vs)::fs , v' | S k ↓
| term_bif_step v v' (H : VALCLOSED v) hd tl vs (H2 : Forall (fun v => VALCLOSED v) vs) (H' : VALCLOSED v') fs k :
  | (FBIF2 v tl (vs ++ [v']))::fs, hd | k ↓ -> | (FBIF2 v (hd::tl) vs)::fs , v' | S k ↓
| term_plus (i1 i2 : Z) fs k :
  | fs, ELit (Z.add i1 i2) | k ↓ ->
  | (FBIF2 (ELit "+"%string) [] ([ELit (Int i1)]))::fs, ELit (Int i2) | S k ↓

| term_app2 v vl e vs fs (H2 : Forall (fun v => VALCLOSED v) vs) k :
  length vl = S (length vs) -> VALCLOSED v -> | fs, e.[list_subst (EFun vl e  :: (vs ++ [v])) idsubst] | k ↓ 
-> | (FApp2 (EFun vl e) [] vs)::fs, v | S k ↓
| term_cons1 e1 v2 fs k (H: VALCLOSED v2):
  | FCons2 v2::fs, e1 | k ↓ -> | FCons1 e1 :: fs, v2 | S k ↓
| term_cons2 v1 v2 fs k (H: VALCLOSED v2) (H0 : VALCLOSED v1):
  | fs, VCons v1 v2 | k ↓ -> | FCons2 v2 :: fs, v1 | S k ↓

| term_case e e1 e2 fs k p : | (FCase p e1 e2)::fs, e | k ↓ -> | fs, ECase e p e1 e2 | S k ↓
| term_app e vs fs k : | (FApp1 vs)::fs, e | k ↓ -> | fs, EApp e vs | S k ↓
| term_bif e vs fs k : | (FBIF1 vs)::fs, e | k ↓ -> | fs, EBIF e vs | S k ↓
| term_let v e1 e2 fs k : | (FLet v e2)::fs, e1 | k ↓ -> | fs, ELet v e1 e2 | S k ↓
| term_cons fs e1 e2 k :
  | FCons1 e1 :: fs, e2 | k ↓ -> | fs, ECons e1 e2 | S k ↓
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
      clear H0. inversion H3; subst.
      1-7, 10-18: try econstructor; eauto.
      * eapply term_case_true; eauto.
      * apply term_case_false; auto.
    }
    {
      inversion H; subst; clear H.
      3-12: try match goal with
      | [ H1 : | _, _ | _ ↓ |- _] => 
         apply IHk in H1; destruct H1 as [e0 [H1e H1k]]; econstructor; split; 
           [ econstructor; [ constructor | eauto ] | auto ]
      end.
      all : auto.
      * apply IHk in H5. destruct H5, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H5. destruct H5, H.
        econstructor; split. econstructor. apply red_case_false. all: eauto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. eauto. auto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H6. destruct H6, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H5. destruct H5, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H.
        econstructor; split. econstructor. constructor. all: eauto.
      * apply IHk in H3. destruct H3, H.
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
    assert (exists y, ⟨ fs', e' ⟩ -[ n ]-> ⟨ [], y ⟩ /\ VALCLOSED y). { 
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

Corollary term_step_term_plus :
  forall k k2 fs e fs' e', 
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | k2 ↓
->
  | fs, e | k + k2 ↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem.
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0, H0.
  pose proof (transitive_eval _ _ _ _ _ H _ _ _ H0).
  eexists. eauto.
Qed.

Lemma eval_app_partial :
  forall vals vl e v Fs hds (P : VALCLOSED (EFun vl e)), length vl = length (hds ++ v :: vals) ->
  Forall (fun v => VALCLOSED v) vals -> Forall (fun v => VALCLOSED v) hds -> VALCLOSED v ->
  ⟨ FApp2 (EFun vl e) vals hds :: Fs, v ⟩ -[S (length vals)]-> ⟨ Fs , e.[list_subst (EFun vl e :: (hds ++ v :: vals)) idsubst]⟩.
Proof.
  induction vals; intros.
  * simpl. econstructor. constructor; auto. rewrite app_length in H. simpl in H. lia.
    constructor.
  * simpl. econstructor. constructor; auto. inversion H0. subst.
    epose proof (IHvals vl e a _ (hds ++ [v]) _ _ H6 _ H5). rewrite <- app_assoc in H3.
    exact H3.
  Unshelve.
    auto.
    rewrite <- app_assoc. auto. apply Forall_app. split. auto. constructor; auto.
Qed.

Lemma app1_eval :
  forall vals Fs vl e (P : VALCLOSED (EFun vl e)), Forall (fun v => VALCLOSED v) vals -> length vl = length vals ->
  exists k : nat,
  ⟨ [FApp1 vals] ++ Fs, EFun vl e ⟩ -[ k ]-> ⟨ Fs, e.[EFun vl e .: list_subst vals idsubst] ⟩.
Proof.
  destruct vals; intros.
  * apply length_zero_iff_nil in H0. subst. exists 1. econstructor.
    simpl. constructor. cbn. constructor.
  * exists (S (S (length vals))). simpl. econstructor. constructor. auto.
    inversion H. subst.
    apply eval_app_partial; auto.
Qed.

Lemma eval_app_partial_core :
  forall hds' vals vl e e' v Fs hds (P : VALCLOSED (EFun vl e)),
  Forall (fun v => VALCLOSED v) hds -> Forall (fun v => VALCLOSED v) hds' -> VALCLOSED v ->
  ⟨ FApp2 (EFun vl e) (hds' ++ e' :: vals) hds :: Fs, v ⟩ -[S (length hds')]-> 
  ⟨ FApp2 (EFun vl e) vals (hds ++ v :: hds') :: Fs , e'⟩.
Proof.
  induction hds'; intros.
  * simpl. econstructor. constructor; auto. constructor.
  * simpl. econstructor. constructor; auto. inversion H0. subst.
    epose proof (IHhds' vals vl e _ a Fs (hds ++ [v]) _ _ _ H4).
    rewrite <- app_assoc in H2. exact H2.
  Unshelve.
    auto.
    apply Forall_app. split; auto. auto.
Qed.

Lemma full_eval_app_partial : forall e vals vl Fs (P : VALCLOSED (EFun vl e)),
  length vl = length vals -> Forall (fun v => VALCLOSED v) vals ->
  ⟨ Fs, EApp (EFun vl e) vals ⟩ -[2 + length vals]-> ⟨ Fs, e.[EFun vl e .: list_subst vals idsubst] ⟩.
Proof.
  destruct vals; intros.
  - simpl. apply length_zero_iff_nil in H. subst. econstructor. constructor.
    econstructor. constructor. constructor.
  - simpl. econstructor. constructor.
    econstructor. constructor. auto. inversion H0.
    apply eval_app_partial; auto.
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

Theorem app_term_fun : forall tl k hds e e' Fs (P : EXPCLOSED e)   (PP : Forall (fun v => EXPCLOSED v) tl),
  | FApp2 e' tl hds :: Fs, e | k ↓ ->
  Forall (fun v => VALCLOSED v) hds ->
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    EXPCLOSED e -> | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), VALCLOSED v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩)
->
  exists vl b, e' = EFun vl b /\ length vl = S (length (hds ++ tl)).
Proof.
  induction tl; intros.
  * apply H1 in H as H'. 2: lia. destruct H', H2, H2.
    eapply terminates_step_any_2 in H. 2: exact H3.
    inversion H; subst; try inversion_is_value.
    rewrite app_length, Nat.add_0_r. do 2 eexists. split. reflexivity. auto.
    congruence.
  * apply H1 in H as H'; auto. destruct H', H2, H2.
    eapply terminates_step_any_2 in H. 2: exact H3.
    inversion H; subst; try inversion_is_value.
    apply H1 in H13 as H''. 2: lia. destruct H'', H4, H4.
    eapply terminates_step_any_2 in H13. 2: exact H5.
    apply IHtl in H13. destruct H13, H6, H6. subst. exists x3, x4. split; auto.
    repeat rewrite app_length in *. simpl in *. lia.
    3: apply Forall_app; auto.
    2,4: inversion PP; auto.
    constructor. auto.
    intros. eapply H1. 3: exact H8. lia. auto.
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
    1-8, 10-18: simpl; econstructor; try constructor; auto.
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
    exists (v : Exp) (k : nat), VALCLOSED v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩ /\ k <= m) ->
  | FApp2 x0 tl hds :: Fs, e | k ↓ -> k > length tl.
Proof.
  induction tl; intros.
  * inversion H0; simpl; lia.
  * simpl. apply H in H0 as H0'. destruct H0', H1, H1, H2.
    eapply (terminates_step_any_2 _ _ _ _ H0) in H2 as H2'.
    inversion H2'; subst; try inversion_is_value.
    eapply IHtl in H13. lia. intros. apply H. lia. auto. lia.
Qed.

Lemma eval_app_partial_core_2 :
  forall hds' vals vl e e' v Fs hds k (P : VALCLOSED (EFun vl e)) (PP : Forall (fun v => EXPCLOSED v) hds'),
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    EXPCLOSED e -> | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat), VALCLOSED v /\ ⟨ Fs, e ⟩ -[ k ]-> ⟨ Fs, v ⟩) ->
  | FApp2 (EFun vl e) (hds' ++ e' :: vals) hds :: Fs, v | k ↓ ->
  VALCLOSED v ->
  Forall (fun v => VALCLOSED v) hds ->
  exists k0 hds'', k0 <= k /\ Forall (fun v => VALCLOSED v) hds'' /\
  ⟨ FApp2 (EFun vl e) (hds' ++ e' :: vals) hds :: Fs, v ⟩ -[k0]-> 
  ⟨ FApp2 (EFun vl e) vals (hds ++ v :: hds'') :: Fs , e'⟩.
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
      assert (⟨ FApp2 (EFun vl e) (e' :: vals) (hds ++ [v]) :: Fs, x ⟩ -[1]->
           ⟨ FApp2 (EFun vl e) vals ((hds ++ [v]) ++ [x]) :: Fs, e' ⟩).
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
Qed.

Lemma eval_app_partial_core_emtpy :
  forall hds' vals vfun e' v Fs hds k (P : VALCLOSED vfun) (PP : Forall (fun v => EXPCLOSED v) hds'),
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    EXPCLOSED e -> | Fs, e | m ↓ 
    -> exists (v : Exp) (k : nat), VALCLOSED v /\ ⟨ [], e ⟩ -[ k ]-> ⟨ [], v ⟩) ->
  | FApp2 vfun (hds' ++ e' :: vals) hds :: Fs, v | k ↓ ->
  VALCLOSED v ->
  Forall (fun v => VALCLOSED v) hds ->
  exists k0 hds'', k0 <= k /\ Forall (fun v => VALCLOSED v) hds'' /\
  ⟨ [FApp2 vfun (hds' ++ e' :: vals) hds], v ⟩ -[k0]-> 
  ⟨ [FApp2 vfun vals (hds ++ v :: hds'')] , e'⟩.
Proof.
  induction hds'; intros.
  * simpl in *. inversion H0; subst; try inversion_is_value.
    exists 1, []. split. lia. split. auto. econstructor. constructor; auto. constructor.
  * simpl in *. inversion H0; subst; try inversion_is_value.
    apply H in H12 as P1. 2: lia. destruct P1, H3, H3.
    eapply frame_indep_nil in H4 as H4_1.
    eapply (terminates_step_any_2 _ _ _ _ H12) in H4_1 as H4'.
    inversion H4'; subst; try inversion_is_value.
    2: { destruct hds'; inversion H6. }
    destruct hds'; simpl in H6; inversion H6; subst.
    - simpl in H4.
      assert (⟨ [FApp2 vfun (e' :: vals) (hds ++ [v])], x ⟩ -[1]->
           ⟨ [FApp2 vfun vals ((hds ++ [v]) ++ [x])], e' ⟩).
           { do 2 econstructor; auto. }
      eapply frame_indep_nil in H4.
      epose proof (transitive_eval _ _ _ _ _ H4 _ _ _ H5).
      exists (S (x0 + 1)), [x]. split. lia. split. auto.
      econstructor. constructor; auto.
      rewrite <- app_assoc in H7. simpl in H7. auto.
    - epose proof (IHhds' vals vfun e' x Fs _ _ _ _ _ H4' H'0 H15).
      Unshelve. 4: { intros. eapply H. 3: exact H8. lia. auto. }
      destruct H5, H5, H5, H7.
      eapply frame_indep_nil in H4.
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
Qed.

Lemma term_bif_eval_empty :
  forall tl Fs v0 vals lst hd k,
  (forall m : nat,
    m < S k ->
    forall (Fs : FrameStack) (e : Exp),
    EXPCLOSED e ->
    | Fs, e | m ↓ ->
    exists (v : Exp) (k : nat),
      VALCLOSED v /\
      ⟨ [], e ⟩ -[ k ]-> ⟨ [], v ⟩) ->
  | FBIF2 v0 (tl ++ [lst]) vals :: Fs, hd | k ↓ ->
  VALCLOSED hd ->
  Forall (fun e => EXPCLOSED e) tl ->
  Forall (fun e => VALCLOSED e) vals ->
  exists i vals', i <= k /\ Forall (fun v => VALCLOSED v) vals' /\
    ⟨ FBIF2 v0 (tl ++ [lst]) vals :: [], hd ⟩ -[i]->
    ⟨ FBIF2 v0 [] (vals ++ [hd] ++ vals') :: [], lst ⟩.
Proof.
  induction tl; intros; simpl.
  * inversion H0; subst; try inversion_is_value.
    exists 1, []. split. 2: split. 2: auto.
    lia.
    econstructor. constructor; auto. constructor.
  * inversion H2; subst.
    inversion H0; subst; try inversion_is_value.
    apply H in H15 as HH; auto. destruct HH as [v1 [k1 [v1cl HH]]].
    eapply frame_indep_nil in HH as HH0.
    eapply (terminates_step_any_2 _ _ _ _ H15) in HH0 as HH'; auto.
    destruct (k0 - k1) eqn:Eq. inversion HH'.
    epose proof (IHtl Fs v0 (vals ++ [hd]) lst v1 (S n) _ HH' v1cl H7 _).
    destruct H4 as [k2 [vals' [Hlt [Fcl H4]]]].
    exists (S (k1 + k2)), (v1 :: vals').
    split. 2: split. lia.
    constructor; auto.
    econstructor. constructor; auto.
    eapply transitive_eval.
    eapply frame_indep_nil in HH. exact HH.
    simpl in H4.
    rewrite <- app_assoc in H4. exact H4.
  Unshelve.
    intros. eapply H. 3: exact H8. lia. auto. apply Forall_app; auto.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
Theorem term_eval_empty : forall x Fs e (P : EXPCLOSED e), | Fs, e | x ↓ ->
  exists v k, VALCLOSED v /\ ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ (* /\ k <= x *).
Proof.
  induction x using lt_wf_ind. destruct x; intros; inversion H0; subst; try congruence.
  * exists e, 0. now repeat constructor.
  * exists e, 0. split; [ auto | do 2 constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor].
  * apply H in H4. destruct H4, H1, H1. exists x0, (S x1).
    split; [ auto | ]. econstructor. constructor. auto. lia.
    inversion P. 2: inversion_is_value. apply -> subst_preserves_scope_exp; eauto.
  * exists e, 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * exists (EFun [] e0), 0. inversion P. split; [ auto | do 2 constructor].
  * exists e, 0. split; [ auto | now constructor].
  * exists e, 0. split; [ auto | now constructor ].
  * exists (ELit i2), 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * exists e, 0. split; [ auto | now constructor ].
  * apply H in H4 as HH. destruct HH, H1, H1. 2: lia.
    eapply frame_indep_nil in H2 as H2_1.
    eapply (terminates_step_any_2 _ _ _ _ H4) in H2_1 as H2'.
    inversion H2'; subst; try inversion_is_value.
    - apply H in H12. 2: lia. destruct H12, H3, H3.
      exists x2, (S (x1 + S x3)). split. auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      eapply frame_indep_nil in H2. exact H2.
      econstructor. constructor. all: eauto. inversion P. 2: inversion_is_value.
      subst. apply -> subst_preserves_scope_exp. exact H13.
      rewrite (match_pattern_length _ _ _ H11), Nat.add_0_r.
      eapply scoped_list_idsubst, match_pattern_scoped. exact H9. eauto.
    - apply H in H12. 2: lia. destruct H12, H3, H3.
      exists x2, (S (x1 + S x3)). split. auto.
      econstructor. constructor. eapply transitive_eval; eauto.
      eapply frame_indep_nil in H2. exact H2.
      econstructor. apply red_case_false; auto. auto. now inversion P.
    - now inversion P.
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
        assert (⟨ [FApp2 (EFun vl e1) [] []], x2 ⟩ -[1]-> ⟨ [], e1.[list_subst (EFun vl e1 :: [] ++ [x2]) idsubst] ⟩).
        { repeat econstructor; auto. }
        eapply frame_indep_nil in H7.
        epose proof (transitive_eval _ _ _ _ _ H10 _ _ _ H7).
        assert (⟨ [FApp1 [e]], EFun vl e1 ⟩ -[1]-> ⟨ [FApp2 (EFun vl e1) [] []], e ⟩). { do 2 econstructor; auto. }
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
        assert (⟨ [FApp2 (EFun vl e1) [] (x2 :: x7)], x8 ⟩ -[1]->
              ⟨ [], e1.[list_subst (EFun vl e1 :: (x2 :: x7) ++ [x8]) idsubst] ⟩). { econstructor. constructor; auto. constructor. }
        epose proof (transitive_eval _ _ _ _ _ H15 _ _ _ H18).
        epose proof (transitive_eval _ _ _ _ _ H21 _ _ _ H14).
        eapply frame_indep_nil in H5.
        epose proof (transitive_eval _ _ _ _ _ H5 _ _ _ H22).
        assert (⟨ [FApp1 (e :: x4 ++ [x5])], EFun vl e1 ⟩ -[1]->
            ⟨ [FApp2 (EFun vl e1) (x4 ++ [x5]) []] , e ⟩).
            { econstructor. constructor. auto. constructor. }
        simpl app in *.
        epose proof (transitive_eval _ _ _ _ _ H24 _ _ _ H23).
        eapply frame_indep_nil in H2.
        epose proof (transitive_eval _ _ _ _ _ H2 _ _ _ H25).

        exists x0, (S (x1 + (1 + (x3 + (x6 + x9 + 1 + x10))))). split; auto.
        econstructor. constructor. auto.
     Unshelve.
       ** inversion H1. subst. apply -> subst_preserves_scope_exp; eauto.
          replace (S (Datatypes.length vl) + 0) with (length ((EFun vl e1 :: (x2 :: x7) ++ [x8]))). 2: { simpl. rewrite app_length. simpl in *. lia. }
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
      exists (ELit (i1 + i2)%Z). eexists.
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
  exists vl b, e' = EFun vl b /\ length vl = S (length (hds ++ tl)).
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
  Forall (fun v => VALCLOSED v) l2 /\ exists vl e', v = EFun vl e'.
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

Theorem term_app_in_k : forall Fs vl vals e k (P : VALCLOSED (EFun vl e)),
  length vl = length vals -> Forall (fun v => VALCLOSED v) vals ->
  | Fs, e.[EFun vl e .: list_subst vals idsubst] | k ↓ ->
  | Fs, EApp (EFun vl e) vals | 2 + length vl + k ↓.
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
      assert (⟨ FApp2 (EFun vl e) [] (x :: l') :: Fs, l'x ⟩ -[1]-> ⟨ Fs, e.[EFun vl e .: list_subst (x :: l' ++ [l'x]) idsubst] ⟩). { 
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

