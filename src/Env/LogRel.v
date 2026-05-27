From CoreErlang Require Export Env.Semantics
                               Env.Termination
                               Env.CIU.

Import ListNotations.

Corollary step_terminates_any :
  forall Γ fs e k Γ' fs' e',
    ⟨ Γ, fs, e ⟩ -[k]-> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓ ->
      | Γ, fs, e | ↓.
Proof.
  intros * H H'.
  destruct H'. exists (k + x).
  eapply step_term_term.
  * eassumption.
  * rewrite Nat.add_sub'. assumption.
  * lia.
Qed.

Corollary step_terminates_one :
  forall Γ fs e Γ' fs' e',
    ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓ ->
      | Γ, fs, e | ↓.
Proof.
  intros * H H'.
  eapply step_terminates_any with (k := 1).
  * eapply step_trans.
    + eauto.
    + apply step_refl.
  * auto.
Qed.

Corollary terminates_step_one :
  forall Γ fs e Γ' fs' e',
    | Γ, fs, e | ↓ ->
      ⟨ Γ, fs, e ⟩ --> ⟨ Γ', fs', e' ⟩ ->
      | Γ', fs', e' | ↓.
Proof.
  intros * HT H1.
  Check terminates_step_any.
  eapply terminates_step_any with (k := 1).
  eauto. econstructor. eauto. constructor.
Qed.

Module TakeFour.

Definition frame_rel (n : nat)
                     (Vrel : forall m, m <= n -> Val -> Val -> Prop)
                     (*Γ1 Γ2 : Env*)
                     (F1 F2 : FrameStack) : Prop :=
  FSCLOSED F1 /\ FSCLOSED F2 /\
  forall m (Hmn : m <= n) v1 v2 Γ1 Γ2,
    Vrel m Hmn v1 v2 ->
    | Γ1, F1, v1 | m ↓ -> | Γ2, F2, v2 | ↓.

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Val -> Val -> Prop)
                   (Γ1 Γ2 : Env)
                   (e1 e2 : Exp) : Prop :=
  (* EXPCLOSED e1 /\ EXPCLOSED e2 /\ *)
  EXP (length Γ1) ⊢ e1 /\ EXP (length Γ2) ⊢ e2 /\
  (* ^^^ These are important, since we only give values to variables when we come
         accross them, the expressions need to be scoped in the environment, and
         not closed! Substitutions would result in closed expressions (see: src/LogRel.v),
         but we can't rely on this here. *)
  forall m (Hmn : m <= n) F1 F2,
    frame_rel m (fun m' H => Vrel m' (Nat.le_trans _ _ _ H Hmn)) F1 F2 ->
    | Γ1, F1, e1 | m ↓ -> | Γ2, F2, e2 | ↓.

Fixpoint Vrel_rec (n : nat)
                  (Vrel : forall m, m < n -> Val -> Val -> Prop)
                  (v1 v2 : Val) : Prop :=
  VALCLOSED v1 /\ VALCLOSED v2 /\
  match v1, v2 with
  | VLit l1, VLit l2 => l1 = l2
  | VPid p1, VPid p2 => p1 = p2
  | VNil, VNil => True
  | VCons v11 v12, VCons v21 v22 => 
        Vrel_rec n Vrel v11 v21 /\ Vrel_rec n Vrel v12 v22
  | VClos Γ1 vl1 b1, VClos Γ2 vl2 b2 =>
    if vl1 =? vl2 then
      forall m (Hmn : m < n), forall (vals1 vals2 : list Val),
        length vals1 = vl1 -> length vals2 = vl2 ->
        list_biforall (Vrel m Hmn) vals1 vals2
      ->
        exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
          (VClos Γ1 vl1 b1 :: vals1 ++ Γ1) (VClos Γ2 vl2 b2 :: vals2 ++ Γ2) b1 b2
    else False
  | _, _ => False
  end.

Definition Vrel : nat -> Val -> Val -> Prop :=
  Fix Wf_nat.lt_wf _ Vrel_rec.

Definition Grel (n : nat) (Γ : nat) (Γ1 Γ2 : Env) : Prop :=
  ENVCLOSED Γ1 /\ ENVCLOSED Γ2 /\
  length Γ1 = length Γ2 /\
  (*        ^ This is needed, otherwise envs like [VNil] and [VNil;VNil] would be related!!!
              nth_error would also work, but that would result in pattern matches,
              I think this should work better. *)
  length Γ1 >= Γ /\
  (*        ^ But if we want to avoid nth_error, this is also needed. This is essentially that
              False branch in the match expression of Grel in src/LogRel.v. Without this, all
              related environments would be related in all gammas. This ensures that the nth-s
              are actually picking values from Γ1 and Γ2.
              
              I guess there is a way to circumvent this, which is using different default values
              for the nth-s in the Vrel_fix (like VLit 1%Z and VLit 2%Z), but that looks very ugly
              to me and we'd probably end up needing a helper lemma for length Γ1 < Γ anyway. *)
    forall x, x < Γ ->
        Vrel n (nth x Γ1 VNil) (nth x Γ2 VNil).
        (* ^ Vrel does not need environments, because values don't depend on the environment.
             This is because variables are now expressions. This fact simplifies LogRels quite
             a bit, so these relations aren't that different to the subst semantics' LogRels. *)

(* So, in this style of semantics, it only makes sense to have a closed Vrel and an open Erel. *)

Definition Erel_open (Γ : nat) (e1 e2 : Exp) : Prop :=
  forall n Γ1 Γ2,
    Grel n Γ Γ1 Γ2 ->
    exp_rel n (fun m _ => Vrel m) Γ1 Γ2 e1 e2.

Definition Vrel_open (v1 v2 : Val) : Prop :=
  forall n,
    Vrel n v1 v2.
(* Actually it does make sense to have an open Vrel. For this definition, n is bound in a
   forall. This is essentially the same as the substitution version, but it doesn't use Grel,
   because values do not depend on the environment. This is also why it doesn't need a Γ : nat
   parameter.
*)

(* Definition Erel_open' (e1 e2 : Exp) : Prop :=
  forall n Γ1 Γ2,
    Grel' n Γ1 Γ2 ->
    exp_rel n (fun m _ => Vrel m) Γ1 Γ2 e1 e2. *)

(* As for Frel, I've not used it yet so I don't know if this is correct. There is no open
   version of it in the subst version and I don't yet know where this closed version is used.
*)

Definition Frel (n : nat) (F1 F2 : FrameStack) : Prop :=
    frame_rel n (fun m _ => Vrel m) F1 F2.

Lemma Vrel_rec_pointwise {n : nat} :
  forall (f g : forall m : nat, (m < n)%nat -> Val -> Val -> Prop),
    (forall (m : nat) (p : (m < n)%nat), f m p = g m p) ->
    Vrel_rec n f = Vrel_rec n g.
Proof.
  intros f g H.
  extensionality v1.
  extensionality v2.
  generalize dependent v2.
  induction v1 using Val_ind2 with
  (P := fun e => True)
  (PN := fun nv => True)
  (Q := fun le => True)
  (R := Forall 
        (fun v1 => forall v2, Vrel_rec n f v1 v2 = Vrel_rec n g v1 v2)); auto;
  intros; try destruct v2; unfold Vrel_rec; intros; try reflexivity.
  * f_equal. f_equal. rewrite IHv1_1. rewrite IHv1_2. reflexivity.
  * f_equal. f_equal.
    destruct (vl =? vl0). 2:reflexivity.
    extensionality m.
    extensionality Hmn.
    extensionality vals1.
    extensionality vals2.
    rewrite H.
    extensionality Hl1.
    extensionality Hl2.
    extensionality Hlbfa.
    f_equal.
    extensionality m'.
    extensionality H0.
    apply H.
Qed.

Lemma Vrel_Fix_eq : forall {n : nat} {v1 v2 : Val},
  Vrel n v1 v2
  = 
  Vrel_rec n (fun (m : nat) (_ : m < n) => Vrel m) v1 v2.
Proof.
  intros n v1 v2.
  unfold Vrel.
  rewrite Fix_eq by (auto using Vrel_rec_pointwise).
  reflexivity.
Qed.

Scheme le_dep_ind := Induction for le Sort Prop.

Lemma Vrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {v1 v2 : Val},
    Vrel n v1 v2 ->
    Vrel m v1 v2.
Proof.
  induction 1 using le_dep_ind; intros; eauto.
  generalize dependent v2.
  induction v1 using Val_ind2 with
  (P  := fun e => True)
  (PN := fun n => True)
  (Q  := fun le => True)
  (R  := Forall 
         (fun v1 => forall v2 : Val, Vrel (S m0) v1 v2 -> 
                                     Vrel m v1 v2));
  try destruct v2; intros; intuition.
  * rewrite Vrel_Fix_eq. rewrite Vrel_Fix_eq in H.
    destruct H as [cl1 [cl2 H]].
    split. 2:split. 1-2:auto.
    specialize (IHv1_1 v2_1). specialize (IHv1_2 v2_2).
    do 2 rewrite Vrel_Fix_eq in IHv1_1.
    do 2 rewrite Vrel_Fix_eq in IHv1_2.
    destruct H. split; auto.
  * rewrite Vrel_Fix_eq. rewrite Vrel_Fix_eq in H.
    unfold Vrel_rec at 1. unfold Vrel_rec at 1 in H.
    intuition. destruct (vl =? vl0); auto.
    intros.
    apply H2; auto. lia.
Qed.

Lemma Vrel_closed :
  forall m v1 v2,
    Vrel m v1 v2 ->
      VALCLOSED v1 /\ VALCLOSED v2.
Proof.
  intros m v1 v2 HV.
  rewrite Vrel_Fix_eq in HV.
  destruct v1, v2; destruct HV as [CL1 [CL2 HV]];
  split; auto.
Qed.

Corollary Vrel_closed_l :
  forall m v1 v2,
    Vrel m v1 v2 ->
      VALCLOSED v1.
Proof. apply Vrel_closed. Qed.

Corollary Vrel_closed_r :
  forall m v1 v2,
    Vrel m v1 v2 ->
      VALCLOSED v2.
Proof. apply Vrel_closed. Qed.

Lemma Erel_open_scope :
  forall Γ e1 e2,
    Erel_open Γ e1 e2 ->
      EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros Γ e1 e2 HE.
  unfold Erel_open in HE.
  unfold exp_rel in HE.
  unfold Grel in HE.
  specialize (HE Γ (repeat VNil Γ) (repeat VNil Γ)).
  assert (ENVCLOSED (repeat VNil Γ)) as Hec.
  { clear. induction Γ.
    + simpl. constructor.
    + simpl. apply ENVCLOSED_cons; auto.
  }
  assert 
  ((∀ x : nat, x < Γ → 
    Vrel Γ (nth x (repeat VNil Γ) VNil) (nth x (repeat VNil Γ) VNil))) as Hnth.
  { clear. intros x Hx.
    apply nth_repeat_lt with (a := VNil) (d := VNil) in Hx.
    rewrite Hx.
    rewrite Vrel_Fix_eq. simpl. auto.
  }
  assert (ENVCLOSED (repeat VNil Γ)
  ∧ ENVCLOSED (repeat VNil Γ)
    ∧ length (repeat VNil Γ) = length (repeat VNil Γ)
      ∧ length (repeat VNil Γ) ≥ Γ
        ∧ (∀ x : nat,
             x < Γ → Vrel Γ (nth x (repeat VNil Γ) VNil) (nth x (repeat VNil Γ) VNil))) as HE'.
  { repeat split; auto.
    rewrite repeat_length. lia.
  }
  specialize (HE HE'). clear -HE.
  destruct HE as [E1 [E2 _]].
  rewrite repeat_length in *. auto.
Qed.

Corollary Erel_open_scope_l :
  forall Γ e1 e2,
    Erel_open Γ e1 e2 ->
      EXP Γ ⊢ e1.
Proof. apply Erel_open_scope. Qed.

Corollary Erel_open_scope_r :
  forall Γ e1 e2,
    Erel_open Γ e1 e2 ->
      EXP Γ ⊢ e2.
Proof. apply Erel_open_scope. Qed.

Lemma Grel_closed :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      ENVCLOSED Γ1 /\ ENVCLOSED Γ2.
Proof.
  intros m Γ Γ1 Γ2 HG.
  destruct HG as [E1 [E2 _]]. auto.
Qed.

Corollary Grel_closed_l :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      ENVCLOSED Γ1.
Proof. apply Grel_closed. Qed.

Corollary Grel_closed_r :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      ENVCLOSED Γ2.
Proof. apply Grel_closed. Qed.

Lemma Grel_length_eq :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 = length Γ2.
Proof.
  intros m Γ Γ1 Γ2 HG.
  destruct HG as [_ [_ [Hl _]]]. auto.
Qed.

Lemma Grel_length_ge :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 >= Γ /\ length Γ2 >= Γ.
Proof.
  intros m Γ Γ1 Γ2 HG.
  destruct HG as [_ [_ [Hl [Hle _]]]].
  lia.
Qed.

Corollary Grel_length_ge_l :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 >= Γ.
Proof. apply Grel_length_ge. Qed.

Corollary Grel_length_ge_r :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ2 >= Γ.
Proof. apply Grel_length_ge. Qed.

Lemma Grel_downclosed :
  forall {m n : nat} {Hmn : m <= n} {Γ : nat} {Γ1 Γ2 : Env},
    Grel n Γ Γ1 Γ2 ->
    Grel m Γ Γ1 Γ2.
Proof.
  unfold Grel; intros. intuition.
  eapply Vrel_downclosed.
  apply H4. lia.
  Unshelve. lia.
Qed.

Theorem Vrel_VLit_compat_closed :
  forall m l,
    Vrel m (VLit l) (VLit l).
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. auto.
Qed.

Theorem Vrel_VLit_compat :
  forall l,
    Vrel_open (VLit l) (VLit l).
Proof.
  unfold Vrel_open. intros. apply Vrel_VLit_compat_closed.
Qed.

Theorem Vrel_VPid_compat_closed :
  forall m p,
    Vrel m (VPid p) (VPid p).
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. auto.
Qed.

Theorem Vrel_VPid_compat :
  forall p,
    Vrel_open (VPid p) (VPid p).
Proof.
  unfold Vrel_open. intros. apply Vrel_VPid_compat_closed.
Qed.

Theorem Vrel_VNil_compat_closed :
  forall m,
    Vrel m VNil VNil.
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. auto.
Qed.

Theorem Vrel_VNil_compat :
  Vrel_open VNil VNil.
Proof.
  unfold Vrel_open. intros. apply Vrel_VNil_compat_closed.
Qed.

Theorem Vrel_VCons_compat_closed :
  forall m hd hd' tl tl',
    Vrel m hd hd' -> Vrel m tl tl' ->
    Vrel m (VCons hd tl) (VCons hd' tl').
Proof.
  intros m hd hd' tl tl' Hhd Htl. rewrite Vrel_Fix_eq. simpl.
  split. 2: split.
  1-2: constructor; apply Vrel_closed in Hhd, Htl; destruct Hhd, Htl; auto.
  rewrite Vrel_Fix_eq in Hhd.
  rewrite Vrel_Fix_eq in Htl.
  split; auto.
Qed.

Theorem Vrel_VCons_compat :
  forall hd hd' tl tl',
    Vrel_open hd hd' -> Vrel_open tl tl' ->
    Vrel_open (VCons hd tl) (VCons hd' tl').
Proof.
  unfold Vrel_open. intros. apply Vrel_VCons_compat_closed; auto.
Qed.

Theorem Vrel_VClos_compat_closed :
  forall m Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + length Γ1) b1 b2 ->
    Grel m (length Γ1) Γ1 Γ2 ->
    Vrel m (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
Proof.
  intros m. induction m using Wf_nat.lt_wf_ind.
  intros Γ1  Γ2 vl1 vl2 b1 b2 Hl HE HG. subst.
  rewrite Vrel_Fix_eq. simpl.
  split. 2: split.
  * constructor.
    + intros i Hi. apply Grel_closed_l in HG.
      apply ENVCLOSED_nth; auto.
    + apply Erel_open_scope_l in HE. auto.
  * constructor.
    + intros i Hi. apply Grel_closed_r in HG.
      apply ENVCLOSED_nth; auto.
    + apply Erel_open_scope_r in HE.
      apply Grel_length_eq in HG. rewrite <- HG. auto.
  * rewrite Nat.eqb_refl.
    intros m0 Hm0 vals1 vals2 Hl1 Hl2 Hlbfa.
    epose proof (nH0 := HE m0 _ _ _).
    destruct nH0 as [nCl1 [nCl2 nH0]].
    split. exact nCl1.
    split. exact nCl2.
    intros m1 Hm1 F1 F2 HF D.
    eapply nH0. 3: exact D. lia.
    assumption.
  Unshelve.
    subst.
    assert (Forall (fun v => VALCLOSED v) vals1 /\ Forall (fun v => VALCLOSED v) vals2) as HFvals.
    { clear -Hlbfa.
      generalize dependent vals2.
      induction vals1; intros vals2 Hlbfa.
      * destruct vals2; inv Hlbfa. auto.
      * destruct vals2; inv Hlbfa.
        apply IHvals1 in H4 as [HFvals1 HFvals2].
        apply Vrel_closed in H2 as [HCa HCv]. auto.
    }
    destruct HFvals as [HFvals1 HFvals2].
    apply Erel_open_scope in HE as HE'.
    destruct HE' as [HEb1 HEb2].
    apply Grel_length_eq in HG as HGl.
    apply Grel_closed in HG as HGc.
    destruct HGc as [HGcΓ1 HGcΓ2].
    split. 2: split.
    1-2: rewrite app_comm_cons.
    1-2: apply ENVCLOSED_app.
    2,4: auto.
    1-2: constructor.
    2,4: auto.
    1-2: constructor.
    4: rewrite <- HGl.
    2,4: auto.
    1-2: intros i Hi; apply ENVCLOSED_nth; auto.
    split.
    do 2 rewrite length_cons.
    do 2 rewrite length_app.
    rewrite Hl2, HGl. reflexivity.
    split.
    rewrite length_cons.
    rewrite length_app. lia.
    intros x Hx. simpl in Hx.
    destruct x.
    { simpl. eapply Vrel_downclosed.
      apply H; eauto.
      eapply Grel_downclosed. eauto.
    }
    simpl. apply Nat.succ_lt_mono in Hx.
    clear H b1 b2 HE HEb1 HEb2.
    assert (x < length vals2 + length Γ2) as Hx' by lia.
    rewrite <- length_app in Hx, Hx'.
    apply nth_possibilities_alt with (def := VNil) in Hx, Hx'.
    
    destruct Hx as [Hx|Hx]; destruct Hx' as [Hx'|Hx']; try lia.
    + destruct Hx as [Hnth Hx].
      destruct Hx' as [Hnth' Hx'].
      rewrite Hnth, Hnth'.
      apply indexed_to_biforall with (d1 := VNil) (d2 := VNil) in Hlbfa.
      destruct Hlbfa as [Hlbfa _].
      auto.
    + destruct Hx as [Hnth [Hx Hx0]].
      destruct Hx' as [Hnth' [Hx' Hx0']].
      rewrite Hnth, Hnth'.
      rewrite Hl2.
      remember (x - length vals1) as y.
      unfold Grel in HG.
      destruct HG as [_ [_ [_ [_ HG]]]].
      eapply Vrel_downclosed; eauto.
  Unshelve.
    lia. lia. lia.
Qed.

Theorem Vrel_VClos_compat :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + length Γ1) b1 b2 ->
    (forall m, Grel m (length Γ1) Γ1 Γ2) ->
    (* ^^ is this correct? Would it make sense to define a Grel_open??? *)
    Vrel_open (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
Proof.
  unfold Vrel_open. intros. apply Vrel_VClos_compat_closed; auto.
Qed.

Theorem Erel_Val_compat_helper :
  forall {n v1 v2 Γ1 Γ2},
    Vrel n v1 v2 ->
    exp_rel n (fun m _ => Vrel m) Γ1 Γ2 (˝v1) (˝v2).
Proof.
  intros n v1 v2 Γ1 Γ2 HV.
  unfold exp_rel.
  apply Vrel_closed in HV as HV'.
  destruct HV' as [H1 H2].
  split. 2: split.
  1-2: constructor; auto.
  intros m Hmn F1 F2 [Hcl1 [Hcl2 HF]] D.
  eapply HF; eauto.
  eapply Vrel_downclosed.
  exact HV.
  Unshelve. lia.
Qed.

Theorem Erel_Val_compat :
  forall {Γ v1 v2},
    Vrel_open v1 v2 ->
    Erel_open Γ (˝v1) (˝v2).
Proof.
  unfold Vrel_open, Erel_open. intros.
  apply Erel_Val_compat_helper.
  auto.
Qed.


(* Why are these 2 in the big formalization? *)
(*********************************************)
Theorem Erel_VLit_compat :
  forall Γ l,
    Erel_open Γ (˝ VLit l) (˝ VLit l).
Proof.
  intros. apply Erel_Val_compat.
  apply Vrel_VLit_compat.
Qed.

Theorem Erel_VPid_compat :
  forall Γ p,
    Erel_open Γ (˝ VPid p) (˝ VPid p).
Proof.
  intros. apply Erel_Val_compat.
  apply Vrel_VPid_compat.
Qed.
(*********************************************)

Lemma Erel_EVar_compat :
  forall Γ n,
    n < Γ ->
    Erel_open Γ (EVar n) (EVar n).
Proof.
  intros Γ n H.
  unfold Erel_open.
  intros n0 Γ1 Γ2 HG.
  destruct HG as [ECΓ1 [ECΓ2 [HLeq [HLlt HG]]]].
  specialize (HG n H).
  unfold exp_rel. split. 2:split.
  1,2: do 2 constructor; lia.
  intros m Hm F1 F2 HFR D.
  destruct HFR as [HF1 [HF2 HFR]].
  destruct m; inv D.
  apply nth_lookup_Some with (d := VNil) in H4.
  rewrite H4 in HG.
  eapply step_terminates_one. 1:constructor.
  2: eapply HFR.
  4: exact H5.
  2: lia.
  2: eapply Vrel_downclosed. 2: exact HG.
  assert (n < length Γ2) as Hl by lia.
  (* Is this the easiest way to do this? *)
  pose proof (nth_lookup_or_length Γ2 n VNil).
  destruct H0.
  * auto.
  * lia.
  Unshelve. lia.
Qed.

Lemma Erel_ECons_compat :
  forall Γ e1 e1' e2 e2',
    Erel_open Γ e1 e1' -> Erel_open Γ e2 e2' ->
    Erel_open Γ (ECons e1 e2) (ECons e1' e2').
Proof.
  intros Γ e1 e1' e2 e2' He1 He2.
  unfold Erel_open in *.
  intros n Γ1 Γ2 HG.
  unfold exp_rel.
  apply Grel_length_ge in HG as HG'.
  destruct HG' as [HG1 HG2].
  apply Erel_open_scope in He1 as He1sc.
  destruct He1sc as [He1sc He1'sc].
  apply Erel_open_scope in He2 as He2sc.
  destruct He2sc as [He2sc He2'sc].
  eapply Grel_closed in HG as HC.
  destruct HC as [HCΓ1 HCΓ2].
  split. 2: split.
  1-2: do 2 constructor.
  1-4: eapply scope_ext_app; eauto.
  intros m Hmn F1 F2 HF D.
  destruct HF as [HF1 [HF2 HF]].
  destruct m; inv D.
  unfold exp_rel in He2, He1.
  eapply He2 in H2 as [i D]; eauto.
  eexists. constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  1-2: eapply scope_ext_app; eauto.
  intros m0 Hm0m v1 v2 Γ0 Γ3 HV D.
  apply Vrel_closed in HV as HV'.
  destruct HV' as [Hv1 Hv2].
  inv D.
  eapply He1 in H8 as [i D]; eauto.
  eexists. constructor. exact D. lia.
  split. 2:split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0k v0 v3 Γ4 Γ5 HV' D.
  destruct m0; inv D.
  eapply HF in H6 as [i D].
  eexists. constructor. exact D. lia.
  apply Vrel_VCons_compat_closed; eapply Vrel_downclosed; eauto.
  Unshelve. lia. lia.
Qed.

Lemma Erel_Fun_compat :
  forall Γ (vl vl' : nat) b b',
    vl = vl' ->
    Erel_open (S vl + Γ) b b' ->
    Erel_open Γ (EFun vl b) (EFun vl' b').
Proof.
  intros Γ vl vl' b b' Hvl He. subst.
  unfold Erel_open. intros n Γ1 Γ2 HG.
  apply Grel_length_ge in HG as Hge.
  destruct Hge as [HgeΓ1 HgeΓ2].
  apply Grel_length_eq in HG as Heq.
  apply Grel_closed in HG as Hcl.
  destruct Hcl as [HclΓ1 HclΓ2].
  apply Erel_open_scope in He as Hesc.
  destruct Hesc as [Hbsc Hbsc'].
  split. 2: split.
  1-2: do 2 constructor.
  1-2: eapply scope_ext_app.
  2,4: eauto.
  1-2: lia.
  intros m Hmn F1 F2 HF D.
  unfold frame_rel in HF.
  destruct m; inv D.
  eapply HF in H2 as [i D]; eauto.
  eexists. constructor. exact D.
  
  
  
  
  rewrite Vrel_Fix_eq. simpl.
  split. 2:split.
  1-2: constructor.
  1,3: intros i Hi.
  1-2: apply ENVCLOSED_nth; auto.
  1-2: eapply scope_ext_app.
  2,4: eauto.
  1-2: lia.
  rewrite Nat.eqb_refl.
  intros m0 Hm0n vals1 vals2 Hvals1 Hvals2 Hlbfa.
  unfold Erel_open in He.
  apply He.
  unfold Grel.
  repeat split.
  5: { intros. destruct x.
       * simpl. apply Vrel_VClos_compat_closed; eauto.
         Search b. Print Erel_open. Search Erel_open.
       
Qed.



























