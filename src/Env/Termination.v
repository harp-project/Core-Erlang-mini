From CoreErlang Require Export Env.Semantics
                               Env.ClosedScoping.

Reserved Notation "| G , fs , e | k ↓" (at level 80).
Inductive terminates_in_k : Env -> FrameStack -> Exp -> nat -> Prop :=

| term_val v Γ :
  | Γ, [], ˝v | 0 ↓ 

| term_bif0 Γ0 Γ xs v res k :
  eval v [] = Some res ->
  | Γ, xs, res | k ↓ ->
  | Γ0, (FBIF1 [] Γ)::xs, ˝v | S k ↓

| term_bif Γ0 Γ xs e1 l v k :
  | Γ, FBIF2 v [] l Γ :: xs, e1 | k ↓ ->
  | Γ0, (FBIF1 (e1::l) Γ)::xs, ˝v | S k ↓

| term_bif_params Γ0 Γ xs vl e1 el v v0 k :
  | Γ, FBIF2 v (vl ++ [v0]) el Γ :: xs, e1 | k ↓ ->
  | Γ0, (FBIF2 v vl (e1::el) Γ)::xs, ˝v0 | S k ↓

| term_bif_params_done Γ0 Γ xs vl v v0 res k :
  eval v (vl ++ [v0]) = Some res ->
  | Γ, xs, res | k ↓ ->
  | Γ0, (FBIF2 v vl [] Γ)::xs, ˝v0 | S k ↓

| term_app0 Γ0 Γ xs v Γ' res k :
  beta_reduce v [] = Some (Γ', res) ->
  | Γ', xs, res | k ↓ ->
  | Γ0, (FApp1 [] Γ)::xs, ˝v | S k ↓

| term_app Γ0 Γ xs e1 l v k :
  | Γ, FApp2 v [] l Γ :: xs, e1 | k ↓ ->
  | Γ0, (FApp1 (e1::l) Γ)::xs, ˝v | S k ↓

| term_app_params Γ0 Γ xs vl e1 el v v0 k :
  | Γ, FApp2 v (vl ++ [v0]) el Γ :: xs, e1 | k ↓ ->
  | Γ0, (FApp2 v vl (e1::el) Γ)::xs, ˝v0 | S k ↓

| term_app_params_done Γ0 Γ xs vl v v0 Γ' res k :
  beta_reduce v (vl ++ [v0]) = Some (Γ', res) ->
  | Γ', xs, res | k ↓ ->
  | Γ0, (FApp2 v vl [] Γ)::xs, ˝v0 | S k ↓

| term_let Γ0 Γ val e2 xs k :
  | val :: Γ, xs, e2 | k ↓ ->
  | Γ0, (FLet e2 Γ)::xs, ˝val | S k ↓

| term_case_true Γ0 Γ e2 e3 v p xs l k :
  match_pattern p v = Some l ->
  | l ++ Γ, xs, e2 | k ↓ ->
  | Γ0, (FCase p e2 e3 Γ)::xs, ˝v | S k ↓

| term_case_false Γ0 Γ e2 e3 p v xs k :
  match_pattern p v = None ->
  | Γ, xs, e3 | k ↓ ->
  | Γ0, (FCase p e2 e3 Γ)::xs, ˝v | S k ↓

| term_cons1 Γ0 Γ xs v2 e1 k :
  | Γ, FCons2 v2 Γ::xs, e1 | k ↓ ->
  | Γ0, FCons1 e1 Γ::xs, ˝v2 | S k ↓

| term_cons2 Γ0 Γ xs v2 v1 k :
  | Γ, xs, VCons v1 v2 | k ↓ ->
  | Γ0, FCons2 v2 Γ::xs, ˝v1 | S k ↓

(** Steps *)
| term_step_let Γ xs e1 e2 k :
  | Γ, (FLet e2 Γ)::xs, e1 | k ↓ ->
  | Γ, xs, ELet e1 e2 | S k ↓
| term_step_app Γ xs e el k :
  | Γ, (FApp1 el Γ)::xs, e | k ↓ ->
  | Γ, xs, EApp e el | S k ↓
| term_step_bif Γ fs name params k :
  | Γ, FBIF1 params Γ :: fs, name | k ↓ ->
  | Γ, fs, EBIF name params | S k ↓
| term_step_case Γ xs e1 p e2 e3 k :
  | Γ, (FCase p e2 e3 Γ)::xs, e1 | k ↓ ->
  | Γ, xs, ECase e1 p e2 e3 | S k ↓
| term_step_cons Γ xs e1 e2 k :
  | Γ, (FCons1 e1 Γ) :: xs, e2 | k ↓ ->
  | Γ, xs, ECons e1 e2 | S k ↓

(** Additional rules to handle environments *)
| term_fun Γ xs vl e k :
  | Γ, xs, VClos Γ vl e | k ↓ ->
  | Γ, xs, EFun vl e | S k ↓

| term_var Γ xs x (val : Val) k :
  Γ !! x = Some val ->
  | Γ, xs, ˝val | k ↓ ->
  | Γ, xs, EVar x | S k ↓
where "| G , fs , e | k ↓" := (terminates_in_k G fs e k) : env_scope.

Definition terminates Γ fs e := exists k, | Γ, fs, e | k ↓.
Notation "| G , fs , e | ↓" := (terminates G fs e) (at level 80) : env_scope.

Definition terminates_sem Γ fs e v :=
  exists k Γ', ⟨Γ, fs, e⟩ -[k]-> ⟨Γ', [], ˝v⟩.

Notation "⟨ Γ , fs , e ⟩ -->* v" := (terminates_sem Γ fs e v) (at level 50) : env_scope.

Theorem termination_semantics :
  forall Γ fs e k, | Γ , fs , e | k ↓ ->
    exists Γ' v, ⟨ Γ , fs , e ⟩ -[k]-> ⟨Γ', [], ˝v⟩.
Proof.
  intros Γ fs e k Hterm.
  induction Hterm.
  - exists Γ, v. constructor.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif0. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_bif_params.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_bif_params. exact H.
    + exact IH.
  - destruct IHHterm as [Γ'' [v' IH]].
    exists Γ'', v'. eapply step_trans.
    + apply red_app0. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_app.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_app_params.
    + exact IH.
  - destruct IHHterm as [Γ'' [v' IH]].
    exists Γ'', v'. eapply step_trans.
    + apply red_app_params. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_let.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_case_true. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_case_false. exact H.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_cons1.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_cons2.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_let.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_app.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_bif.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_case.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply step_cons.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_fun.
    + exact IH.
  - destruct IHHterm as [Γ' [v' IH]].
    exists Γ', v'. eapply step_trans.
    + apply red_var. exact H.
    + exact IH.
Qed.

Theorem semantics_termination :
  forall k Γ fs e v Γ', ⟨ Γ , fs , e ⟩ -[k]-> ⟨Γ', [], ˝v ⟩ ->
    | Γ , fs , e | k ↓.
Proof.
  intros k.
  induction k; intros Γ fs e Γ' v Hrt; inv Hrt.
  * constructor.
  * inv H0. all: try by (constructor; eapply IHk; eassumption).
    all: try by (econstructor; [ eassumption | eapply IHk; eassumption]).
Qed.

Corollary terminates_semantics :
  forall Γ fs e, | Γ , fs , e | ↓ ->
    exists v, ⟨ Γ , fs , e ⟩ -->* v.
Proof.
  intros Γ fs e [k Hterm].
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ' [v Hsteps]].
  exists v. exists k, Γ'. exact Hsteps.
Qed.

Corollary semantics_terminates :
  forall Γ fs e v, ⟨ Γ , fs , e ⟩ -->* v ->
    | Γ , fs , e | ↓.
Proof.
  intros Γ fs e v [k [Γ' Hsteps]].
  exists k. eapply semantics_termination. exact Hsteps.
Qed.

Corollary transitive_eval :
  forall k Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
    forall k' Γ'' fs'' e'',
      ⟨ Γ', fs', e' ⟩ -[k']-> ⟨ Γ'', fs'', e'' ⟩ ->
      ⟨ Γ, fs, e ⟩ -[k + k']-> ⟨ Γ'', fs'', e'' ⟩.
Proof.
  intros k Γ fs e Γ' fs' e' Hrt.
  induction Hrt; intros k' Γ1 fs1 e1 Hrt'; simpl.
  - exact Hrt'.
  - econstructor.
    + exact H.
    + eapply IHHrt. exact Hrt'.
Qed.

Corollary step_term_term :
  forall k n Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
    | Γ', fs', e' | n - k ↓ ->
    n >= k ->
    | Γ, fs, e | n ↓.
Proof.
  intros k n Γ fs e Γ' fs' e' Hrt Hterm Hge.
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ'' [v Hrt']].
  eapply semantics_termination.
  replace n with (k + (n - k)) by lia.
  eapply transitive_eval; eauto.
Qed.

Corollary step_term_term_plus :
  forall k k2 Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
    | Γ', fs', e' | k2 ↓ ->
    | Γ, fs, e | k + k2 ↓.
Proof.
  intros k k2 Γ fs e Γ' fs' e' Hrt Hterm.
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ'' [v Hrt']].
  eapply semantics_termination.
  eapply transitive_eval; eauto.
Qed.

Theorem terminates_step_2 :
  forall n Γ fs e,
    | Γ, fs, e | n ↓ ->
    forall Γ' fs' e',
      ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | n - 1 ↓.
Proof.
  intros n Γ fs e Hterm Γ' fs' e' Hstep.
  destruct n as [|n].
  - inversion Hterm; subst. exfalso. eapply value_nostep. exact Hstep.
  - destruct (termination_semantics _ _ _ _ Hterm) as [Γf [v Hfull]].
    inversion Hfull; subst.
    match goal with
    | Hs : ⟨ _, _, _ ⟩ --> ⟨ _, _, _ ⟩,
      Htail : ⟨ _, _, _ ⟩ -[ _ ]-> ⟨ _, _, _ ⟩ |- _ =>
        pose proof (step_determinism _ _ _ _ _ _ Hstep _ _ _ Hs) as [-> [-> ->]];
        replace (S n - 1) with n by lia;
        eapply semantics_termination;
        exact Htail
    end.
Qed.

Corollary terminates_step_any :
  forall Γ fs e,
    | Γ, fs, e | ↓ ->
    forall k Γ' fs' e',
      ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓.
Proof.
  intros Γ fs e Hterm k Γ' fs' e' Hpre.
  assert (Hstep_term :
    forall Γ0 fs0 e0 Γ1 fs1 e1,
      | Γ0, fs0, e0 | ↓ ->
      ⟨ Γ0, fs0, e0 ⟩ --> ⟨ Γ1, fs1, e1 ⟩ ->
      | Γ1, fs1, e1 | ↓).
  {
    intros Γ0 fs0 e0 Γ1 fs1 e1 [n Hn] Hstep.
    destruct (termination_semantics _ _ _ _ Hn) as [Γf [v Hfull]].
    inversion Hfull; subst.
    - inversion Hn; subst. exfalso. eapply value_nostep. exact Hstep.
    - match goal with
        | Hs : ⟨ _, _, _ ⟩ --> ⟨ _, _, _ ⟩,
          Htail : ⟨ _, _, _ ⟩ -[ _ ]-> ⟨ _, _, _ ⟩ |- _ =>
            pose proof (step_determinism _ _ _ _ _ _ Hstep _ _ _ Hs) as [-> [-> ->]];
            eapply semantics_terminates;
            exists k0, Γf;
            exact Htail
      end.
  }
  induction Hpre.
  - exact Hterm.
  - eapply IHHpre.
    eapply Hstep_term; eauto.
Qed.

Corollary terminates_step_any_2 :
  forall k n Γ fs e,
    | Γ, fs, e | n ↓ ->
    forall Γ' fs' e',
      ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | n - k ↓.
Proof.
  induction k; intros n Γ fs e Hterm Γ' fs' e' Hrt; inversion Hrt; subst.
  - rewrite Nat.sub_0_r. exact Hterm.
  - match goal with
      | Hs : ⟨ _, _, _ ⟩ --> ⟨ _, _, _ ⟩,
        Htail : ⟨ _, _, _ ⟩ -[ k ]-> ⟨ _, _, _ ⟩ |- _ =>
          apply terminates_step_2 with (n := n) in Hs;
          [| exact Hterm];
          eapply IHk in Htail; [| exact Hs];
          replace (n - S k) with ((n - 1) - k) by lia;
          exact Htail
    end.
Qed.

Lemma term_eval_helper_app :
  forall hds' hds e' k vals v Γ Γapp Fs v1,
  (∀ m : nat,
    m < S k
    → ∀ (Γ : list Val) (Fs : FrameStack) (e : Exp),
        AEXP length Γ ⊢ e
        → FSCLOSED Fs
          → ENVCLOSED Γ
            → | Γ, Fs, e | m ↓
              → ∃ (v : Val) (k : nat) (Γ' : Env),
                  VALCLOSED v
                  ∧ ⟨ Γ, [], e ⟩ -[ k ]-> ⟨ Γ', [], ˝ v ⟩
                    ∧ k ≤ m) ->
  Forall (fun e => EXP length Γapp ⊢ e) hds' ->
  Forall (fun e => EXP length Γapp ⊢ e) hds ->
  Forall (fun v => VALCLOSED v) vals ->
  ENVCLOSED Γapp ->
  EXP length Γapp ⊢ e' ->
  VALCLOSED v ->
  VALCLOSED v1 ->
  FSCLOSED Fs ->
  | Γ, FApp2 v vals (hds' ++ e' :: hds) Γapp :: Fs, ˝v1 | k ↓ ->
  exists k0 hds'' (* Γ' *),
  Forall (fun v => VALCLOSED v) hds'' /\
  ⟨ Γ, [FApp2 v vals (hds' ++ e' :: hds) Γapp], ˝v1 ⟩ -[k0]-> 
  ⟨ Γapp, [FApp2 v (vals ++ v1 :: hds'') hds Γapp] , e'⟩ /\ k0 <= k.
Proof.
  induction hds'; intros; simpl.
  * inv H8. do 2 eexists. repeat split.
    2: {
      econstructor. constructor. constructor.
    }
    by auto.
    lia.
  * inv H8. inv H0.
    eapply H in H18 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: try by auto.
      apply Forall_app; split; try assumption. by auto.
      apply Forall_app. split; try assumption.
      by constructor.
    }
    destruct D' as [v' [k' [Γ' [Hv' [HD' Hlt']]]]].
    eapply terminates_step_any_2 in H18. 2: {
      eapply frame_indep_core in HD'. exact HD'.
    }
    simpl in H18.
    apply (IHhds' hds e' (k0 - k') (vals ++ [v1])
                v Γ' Γapp Fs v') in H18 as D''; try by auto.
    2: {
      intros. eapply H; try eassumption. lia.
    }
    2: apply Forall_app; split; by auto.
    destruct D'' as [v'' [k'' [Hv'' [HD'' Hlt'']]]].
    eapply terminates_step_any_2 in H18. 2: {
      eapply frame_indep_core in HD''. exact HD''.
    }
    do 2 eexists. repeat split.
    2: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD'. exact HD'.
      simpl. rewrite <- app_assoc in HD''. simpl in HD''.
      exact HD''.
    }
    by constructor.
    lia.
Qed.

Lemma term_eval_helper_bif :
  forall hds' hds e' k vals v Γ Γapp Fs v1,
  (∀ m : nat,
    m < S k
    → ∀ (Γ : list Val) (Fs : FrameStack) (e : Exp),
        AEXP length Γ ⊢ e
        → FSCLOSED Fs
          → ENVCLOSED Γ
            → | Γ, Fs, e | m ↓
              → ∃ (v : Val) (k : nat) (Γ' : Env),
                  VALCLOSED v
                  ∧ ⟨ Γ, [], e ⟩ -[ k ]-> ⟨ Γ', [], ˝ v ⟩
                    ∧ k ≤ m) ->
  Forall (fun e => EXP length Γapp ⊢ e) hds' ->
  Forall (fun e => EXP length Γapp ⊢ e) hds ->
  Forall (fun v => VALCLOSED v) vals ->
  ENVCLOSED Γapp ->
  EXP length Γapp ⊢ e' ->
  VALCLOSED v ->
  VALCLOSED v1 ->
  FSCLOSED Fs ->
  | Γ, FBIF2 v vals (hds' ++ e' :: hds) Γapp :: Fs, ˝v1 | k ↓ ->
  exists k0 hds'' (* Γ' *),
  Forall (fun v => VALCLOSED v) hds'' /\
  ⟨ Γ, [FBIF2 v vals (hds' ++ e' :: hds) Γapp], ˝v1 ⟩ -[k0]-> 
  ⟨ Γapp, [FBIF2 v (vals ++ v1 :: hds'') hds Γapp] , e'⟩ /\ k0 <= k.
Proof.
  induction hds'; intros; simpl.
  * inv H8. do 2 eexists. repeat split.
    2: {
      econstructor. constructor. constructor.
    }
    by auto.
    lia.
  * inv H8. inv H0.
    eapply H in H18 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: try by auto.
      apply Forall_app; split; try assumption. by auto.
      apply Forall_app. split; try assumption.
      by constructor.
    }
    destruct D' as [v' [k' [Γ' [Hv' [HD' Hlt']]]]].
    eapply terminates_step_any_2 in H18. 2: {
      eapply frame_indep_core in HD'. exact HD'.
    }
    simpl in H18.
    apply (IHhds' hds e' (k0 - k') (vals ++ [v1])
                v Γ' Γapp Fs v') in H18 as D''; try by auto.
    2: {
      intros. eapply H; try eassumption. lia.
    }
    2: apply Forall_app; split; by auto.
    destruct D'' as [v'' [k'' [Hv'' [HD'' Hlt'']]]].
    eapply terminates_step_any_2 in H18. 2: {
      eapply frame_indep_core in HD''. exact HD''.
    }
    do 2 eexists. repeat split.
    2: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD'. exact HD'.
      simpl. rewrite <- app_assoc in HD''. simpl in HD''.
      exact HD''.
    }
    by constructor.
    lia.
Qed.


Theorem term_eval_empty :
  forall x Γ Fs e,
    AEXP length Γ ⊢ e ->
    FSCLOSED Fs ->
    ENVCLOSED Γ ->
    | Γ, Fs, e | x ↓ ->
    exists v k Γ',
      VALCLOSED v /\
      ⟨ Γ, [], e ⟩ -[k]-> ⟨ Γ', [], ˝v ⟩ /\ k <= x.
Proof.
  induction x using lt_wf_ind; intros * He HFs HΓ D; inv D.
  all: try by exists v, 0, Γ; repeat split; auto; try constructor; try lia.
  * exists v0, 0, Γ. repeat split; auto; constructor; lia.
  * exists v0, 0, Γ. repeat split; auto; constructor; lia.
  * exists v0, 0, Γ. repeat split; auto; constructor; lia.
  * exists v0, 0, Γ. repeat split; auto; constructor; lia.
  * exists val, 0, Γ. repeat split; auto; constructor; lia.
  * exists v2, 0, Γ. repeat split; auto; constructor; lia.
  * exists v1, 0, Γ. repeat split; auto; constructor; lia.
  * inv He.
    eapply H in H0 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: by auto.
    }
    destruct D' as [v1 [k1 [Γ1 [Hv1 [HD1 Hlt1]]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    eapply H in H4 as D''; auto. 2: lia. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor; auto.
    }
    destruct D'' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
    do 3 eexists. repeat split.
    2: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
      econstructor. constructor.
      eapply frame_indep_core in HD2. exact HD2.
    }
    assumption.
    lia.
  * inv He.
    eapply H in H0 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: try by auto.
      by rewrite indexed_to_forall.
    }
    destruct D' as [v1 [k1 [Γ1 [Hv1 [HD1 Hlt1]]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H10 as D'; auto. 2: {
        lia.
      }
      2: {
        apply beta_reduce_scoped in H6 as [].
        by apply exp_to_any.
        assumption.
        constructor.
      }
      2: {
        apply beta_reduce_scoped in H6 as []; auto.
        constructor.
      }
      destruct D' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      eapply terminates_step_any_2 in H10. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      do 3 eexists. repeat split.
      2: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. constructor. eassumption.
        eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
        constructor.
      }
      assumption.
      lia.
    }
    { (* inductive case *)
      eapply H in H4 as D'. 2: {
        lia.
      }
      2: {
        apply exp_to_any.
        by apply (H5 0 ltac:(simpl; lia)).
      }
      2: {
        constructor; auto.
        constructor; auto.
        rewrite indexed_to_forall. intros.
        by apply (H5 (S i) ltac:(simpl; lia)).
      }
      destruct D' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      eapply terminates_step_any_2 in H4. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      simpl in H4. destruct (length l) eqn:L.
      * (* single parameter: *)
        apply length_zero_iff_nil in L. subst.
        inv H4.
        eapply H in H12 as X; try eassumption. 2: lia.
        2: {
          apply exp_to_any. apply beta_reduce_scoped in H6; try assumption.
          apply H6. apply Forall_app; split; try constructor; auto.
        }
        2: {
          apply beta_reduce_scoped in H6; try assumption.
          apply H6. apply Forall_app; split; try constructor; auto.
        }
        destruct X as [v5 [k5' [Γ5 [Hv5 [HD5 Hlt5]]]]].
        do 3 eexists. repeat split.
        2: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        assumption.
        lia.

        (* more parameters: *)
      * apply eq_sym, last_element_exists in L as [l' [x ?]].
        subst.
        eapply (term_eval_helper_app l' []) in H4 as X; try eassumption.
        all: try by constructor.
        3: {
          rewrite indexed_to_forall.
          intros. specialize (H5 (S i) ltac:(simpl;rewrite length_app;lia)).
          simpl in H5.
          rewrite app_nth1 in H5. 2: lia. eassumption.
        }
        2: {
          intros. eapply H. lia. all: eassumption.
        }
        2: {
          specialize (H5 (S (length l')) ltac:(simpl;rewrite length_app;simpl;lia)).
          simpl in H5.
          rewrite app_nth2 in H5. 2: lia.
          rewrite Nat.sub_diag in H5. eassumption.
        }
        destruct X as [k3 [v3 [Hv3 [HD3 Hlt3]]]].
        eapply terminates_step_any_2 in H4. 2: eapply frame_indep_core in HD3; exact HD3.
        eapply H in H4 as X; try eassumption. 2: { lia. }
        2: {
          apply exp_to_any. specialize (H5 (S (length l')) ltac:(simpl; rewrite length_app; simpl; lia)).
          simpl in H5. rewrite app_nth2 in H5. rewrite Nat.sub_diag in H5. assumption. lia.
        }
        2: {
          apply Forall_app. split; try assumption.
          do 2 constructor; try assumption. 2: constructor.
          simpl. by constructor.
        }
        destruct X as [v4 [k4 [Γ4 [Hv4 [HD4 Hlt4]]]]].
        simpl in H4.
        eapply terminates_step_any_2 in H4. 2: eapply frame_indep_core in HD4; exact HD4.
        simpl in H4. inv H4.
        
        eapply H in H12 as X; try eassumption. 2: lia.
        2: {
          apply exp_to_any. apply beta_reduce_scoped in H6; try assumption.
          apply H6. apply Forall_app; split; try constructor; auto.
        }
        2: {
          apply beta_reduce_scoped in H6; try assumption.
          apply H6. apply Forall_app; split; try constructor; auto.
        }
        destruct X as [v5 [k5' [Γ5 [Hv5 [HD5 Hlt5]]]]].
        
        do 3 eexists. repeat split.
        2: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          eapply transitive_eval. eapply frame_indep_core in HD3. exact HD3.
          simpl.
          eapply transitive_eval. eapply frame_indep_core in HD4. exact HD4.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        assumption.
        lia.
      * assumption.
    }
  * inv He.
    eapply H in H0 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: try by auto.
      by rewrite indexed_to_forall.
    }
    destruct D' as [v1 [k1 [Γ1 [Hv1 [HD1 Hlt1]]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H10 as D'; auto. 2: {
        lia.
      }
      2: {
        apply eval_val_scoped in H6.
        by cbn.
      }
      destruct D' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      eapply terminates_step_any_2 in H10. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      do 3 eexists. repeat split.
      2: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. constructor. eassumption.
        eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
        constructor.
      }
      assumption.
      lia.
    }
    { (* inductive case *)
      eapply H in H4 as D'. 2: {
        lia.
      }
      2: {
        apply exp_to_any.
        by apply (H5 0 ltac:(simpl; lia)).
      }
      2: {
        constructor; auto.
        constructor; auto.
        rewrite indexed_to_forall. intros.
        by apply (H5 (S i) ltac:(simpl; lia)).
      }
      destruct D' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      eapply terminates_step_any_2 in H4. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      simpl in H4. destruct (length l) eqn:L.
      * (* single parameter: *)
        apply length_zero_iff_nil in L. subst.
        inv H4.
        eapply H in H12 as X; try eassumption. 2: lia.
        2: {
          apply exp_to_any. apply eval_val_scoped in H6; try assumption.
          by constructor.
        }
        destruct X as [v5 [k5' [Γ5 [Hv5 [HD5 Hlt5]]]]].
        do 3 eexists. repeat split.
        2: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        assumption.
        lia.

        (* more parameters: *)
      * apply eq_sym, last_element_exists in L as [l' [x ?]].
        subst.
        eapply (term_eval_helper_bif l' []) in H4 as X; try eassumption.
        all: try by constructor.
        3: {
          rewrite indexed_to_forall.
          intros. specialize (H5 (S i) ltac:(simpl;rewrite length_app;lia)).
          simpl in H5.
          rewrite app_nth1 in H5. 2: lia. eassumption.
        }
        2: {
          intros. eapply H. lia. all: eassumption.
        }
        2: {
          specialize (H5 (S (length l')) ltac:(simpl;rewrite length_app;simpl;lia)).
          simpl in H5.
          rewrite app_nth2 in H5. 2: lia.
          rewrite Nat.sub_diag in H5. eassumption.
        }
        destruct X as [k3 [v3 [Hv3 [HD3 Hlt3]]]].
        eapply terminates_step_any_2 in H4. 2: eapply frame_indep_core in HD3; exact HD3.
        eapply H in H4 as X; try eassumption. 2: { lia. }
        2: {
          apply exp_to_any. specialize (H5 (S (length l')) ltac:(simpl; rewrite length_app; simpl; lia)).
          simpl in H5. rewrite app_nth2 in H5. rewrite Nat.sub_diag in H5. assumption. lia.
        }
        2: {
          apply Forall_app. split; try assumption.
          do 2 constructor; try assumption. 2: constructor.
          simpl. by constructor.
        }
        destruct X as [v4 [k4 [Γ4 [Hv4 [HD4 Hlt4]]]]].
        simpl in H4.
        eapply terminates_step_any_2 in H4. 2: eapply frame_indep_core in HD4; exact HD4.
        simpl in H4. inv H4.
        
        eapply H in H12 as X; try eassumption. 2: lia.
        2: {
          apply exp_to_any. apply eval_val_scoped in H6; try assumption.
          by constructor.
        }

        destruct X as [v5 [k5' [Γ5 [Hv5 [HD5 Hlt5]]]]].
        
        do 3 eexists. repeat split.
        2: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          eapply transitive_eval. eapply frame_indep_core in HD3. exact HD3.
          simpl.
          eapply transitive_eval. eapply frame_indep_core in HD4. exact HD4.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        assumption.
        lia.
      * assumption.
    }
  * inv He.
    eapply H in H0 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: by auto.
    }
    destruct D' as [v1 [k1 [Γ1 [Hv1 [HD1 Hlt1]]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H13 as D''; auto. 2: lia. 2: {
        apply exp_to_any.
        rewrite length_app.
        apply match_pattern_length in H5. by rewrite <- H5.
      }
      2: {
        apply ENVCLOSED_app. 2: assumption.
        by eapply match_pattern_scoped.
      }
      destruct D'' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      do 3 eexists. repeat split.
      2: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. apply red_case_true.
        eapply frame_indep_core in HD2.
        eassumption. exact HD2.
      }
      assumption.
      lia.
    }
    {
      eapply H in H13 as D''; auto. 2: lia. 2: {
        by apply exp_to_any.
      }
      destruct D'' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
      do 3 eexists. repeat split.
      2: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. apply red_case_false. assumption.
        eapply frame_indep_core in HD2.
        exact HD2.
      }
      assumption.
      lia.
    }
  * inv He.
    eapply H in H0 as D'; auto. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor. constructor. all: by auto.
    }
    destruct D' as [v1 [k1 [Γ1 [Hv1 [HD1 Hlt1]]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    eapply H in H4 as D''; auto. 2: lia. 2: {
      by apply exp_to_any.
    }
    2: {
      constructor; auto.
      constructor; auto.
    }
    destruct D'' as [v2 [k2 [Γ2 [Hv2 [HD2 Hlt2]]]]].
    do 3 eexists. repeat split.
    2: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
      econstructor. constructor.
      eapply transitive_eval.
      eapply frame_indep_core in HD2. exact HD2.
      econstructor. constructor.
      constructor.
    }
    by constructor.
    eapply terminates_step_any_2 in H4. 2: eapply frame_indep_core in HD2; exact HD2. inv H4.
    lia.
  * do 3 eexists. repeat split.
    2: {
      econstructor. constructor. constructor.
    }
    - inv He. constructor.
      + intros. by apply ENVCLOSED_nth.
      + assumption.
    - lia.
  * do 3 eexists. repeat split.
    2: {
      econstructor. constructor. eassumption. constructor.
    }
    by eapply ENVCLOSED_lookup.
    lia.
Unshelve.
  exact [].
Qed.


(**
  For a value plugged into a frame stack, termination is independent of the
  current ambient environment.
 *)
Lemma value_terminates_in_k_env_indep :
  forall k Γ1 Γ2 fs (v : Val),
    | Γ1, fs, ˝v | k ↓ ->
    | Γ2, fs, ˝v | k ↓.
Proof.
  intros k Γ1 Γ2 fs v Hterm.
  destruct (termination_semantics _ _ _ _ Hterm) as [Γ' [w Hsteps]].
  destruct (value_core_env_indep _ _ _ _ _ _ Hsteps Γ2) as [Γ'' Hsteps'].
  eapply semantics_termination. exact Hsteps'.
Qed.

Corollary value_terminates_env_indep :
  forall Γ1 Γ2 fs (v : Val),
    | Γ1, fs, ˝v | ↓ ->
    | Γ2, fs, ˝v | ↓.
Proof.
  intros Γ1 Γ2 fs v [k Hterm].
  exists k. eapply value_terminates_in_k_env_indep. exact Hterm.
Qed.

Corollary value_terminates_sem_env_indep :
  forall Γ1 Γ2 fs (v w : Val),
    ⟨ Γ1, fs, ˝v ⟩ -->* w ->
    ⟨ Γ2, fs, ˝v ⟩ -->* w.
Proof.
  intros Γ1 Γ2 fs v w [k [Γ' Hsteps]].
  destruct (value_core_env_indep _ _ _ _ _ _ Hsteps Γ2) as [Γ'' Hsteps'].
  exists k, Γ''. exact Hsteps'.
Qed.
