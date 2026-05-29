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
  (*ENVCLOSED Γ1 /\ ENVCLOSED Γ2 /\*)
  length Γ1 = Γ /\
    list_biforall (Vrel n) Γ1 Γ2.

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

Corollary Vrel_biforall_downclosed :
  forall {n m : nat} {Hmn : m <= n} {l1 l2 : list Val},
    list_biforall (Vrel n) l1 l2 ->
    list_biforall (Vrel m) l1 l2.
Proof.
  intros m n Hmn l1.
  induction l1; intros l2 HV.
  * destruct l2; inv HV. constructor.
  * destruct l2; inv HV. constructor; auto.
    eapply Vrel_downclosed. eauto.
    Unshelve. lia.
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
  rewrite repeat_length in HE.
  assert (list_biforall (Vrel Γ) (repeat VNil Γ) (repeat VNil Γ)).
  { clear. 
    remember Γ as k.
    rewrite Heqk at 2 3. clear Heqk.
    induction Γ.
    * simpl. constructor.
    * simpl. apply biforall_cons; auto.
      rewrite Vrel_Fix_eq. simpl. auto.
  }
  assert (Γ = Γ /\ list_biforall (Vrel Γ) (repeat VNil Γ) (repeat VNil Γ))
    as HE' by (split;[lia|auto]).
  specialize (HE HE').
  destruct HE as [HE1 [HE2 _]].
  auto.
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

Lemma Grel_length_eq :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 = length Γ2.
Proof.
  intros m Γ Γ1 Γ2 [_ Hbfa].
  apply biforall_length in Hbfa. auto.
Qed.

Lemma Grel_length :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 = Γ /\ length Γ2 = Γ.
Proof.
  intros m Γ Γ1 Γ2 HG.
  apply Grel_length_eq in HG as HGl.
  unfold Grel in HG. lia.
Qed.

Lemma Grel_length_l :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ1 = Γ.
Proof. apply Grel_length. Qed.

Lemma Grel_length_r :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      length Γ2 = Γ.
Proof. apply Grel_length. Qed.

Lemma Grel_closed :
  forall m Γ Γ1 Γ2,
    Grel m Γ Γ1 Γ2 ->
      ENVCLOSED Γ1 /\ ENVCLOSED Γ2.
Proof.
  intros m Γ.
  induction Γ; intros Γ1 Γ2 HG.
  * apply Grel_length_eq in HG as Hle.
    destruct HG as [Hl Hbfa].
    apply nil_length_inv in Hl. subst.
    simpl in Hle. symmetry in Hle.
    apply nil_length_inv in Hle. subst.
    split; constructor.
  * apply Grel_length_eq in HG as Hle.
    destruct HG as [Hl Hbfa].
    destruct Γ1; try discriminate.
    destruct Γ2; try discriminate.
    Search list_biforall cons.
    inv Hbfa.
    simpl in Hl. inversion Hl.
    assert (Grel m Γ Γ1 Γ2) as HG. { split; auto. }
    apply IHΓ in HG. destruct HG as [HG1 HG2].
    apply Vrel_closed in H2 as [Hvc1 Hvc2].
    split; constructor; auto.
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

Lemma Grel_cons :
  forall m Γ v1 v2 Γ1 Γ2,
    Vrel m v1 v2 ->
    Grel m Γ Γ1 Γ2 ->
    Grel m (S Γ) (v1 :: Γ1) (v2 :: Γ2).
Proof.
  intros m Γ v1 v2 Γ1 Γ2 HV HG.
  unfold Grel in *. destruct HG as [Hl Hbfa].
  split.
  * simpl. rewrite Hl. reflexivity.
  * constructor; auto.
Qed.

Lemma Grel_take_drop :
  forall m Γ Γ' Γ1 Γ2,
    Grel m Γ (take Γ Γ1) (take Γ Γ2) ->
    Grel m Γ' (drop Γ Γ1) (drop Γ Γ2) ->
    Grel m (Γ + Γ') Γ1 Γ2.
Proof.
  intros m Γ Γ' Γ1 Γ2 HGt HGd.
  apply Grel_length_eq in HGt as Hlt'.
  apply Grel_length_eq in HGd as Hld'.
  unfold Grel in *.
  destruct HGt as [Hlt Hbfat].
  destruct HGd as [Hld Hbfad].
  Search take drop.
  pose proof (take_drop Γ Γ1) as HΓ1.
  pose proof (take_drop Γ Γ2) as HΓ2.
  assert (length (take Γ Γ1 ++ drop Γ Γ1) = length Γ1) as Hl1 by (f_equal; auto).
  assert (length (take Γ Γ2 ++ drop Γ Γ2) = length Γ2) as Hl2 by (f_equal; auto).
  rewrite length_app in Hl1, Hl2.
  rewrite Hlt, Hld in Hl1.
  rewrite <- Hlt', <- Hld', Hlt, Hld in Hl2.
  split;[lia|].
  assert (length Γ1 = length Γ2) as Hl by lia.
  clear Hl1 Hl2.
  
  generalize dependent Γ2.
  generalize dependent Γ1.
  induction Γ; intros Γ1 Hlt Hld HΓ1 Γ2 Hbfat Hbfad Hlt' Hld' HΓ2 Hl.
  * simpl in *. rewrite HΓ1 in Hbfad. rewrite HΓ2 in Hbfad. exact Hbfad.
  * destruct Γ1; try discriminate.
    destruct Γ2; try discriminate.
    simpl in *.
    specialize (IHΓ Γ1).
    inv Hlt. specialize (IHΓ H0 eq_refl HΓ1). clear H0.
    specialize (IHΓ Γ2).
    inv Hbfat. specialize (IHΓ H4 Hbfad Hlt' Hld' HΓ2 Hl).
    constructor; auto.
Qed.

Lemma Grel_app :
  forall m Γ Γ' Γ1 Γ1' Γ2 Γ2',
    length Γ1 = Γ ->
    length Γ2 = Γ ->
    Grel m Γ Γ1 Γ2 ->
    Grel m Γ' Γ1' Γ2' ->
    Grel m (Γ + Γ') (Γ1 ++ Γ1') (Γ2 ++ Γ2').
Proof.
  intros m Γ Γ' Γ1 Γ1' Γ2 Γ2' HΓ1 HΓ2 HG1 HG2.
  pose proof (Grel_take_drop m Γ Γ' (Γ1 ++ Γ1') (Γ2 ++ Γ2')) as HG.
  subst.
  rewrite <- HΓ2 in HG at 3. do 2 rewrite take_app_length in HG.
  rewrite <- HΓ2 in HG at 3. do 2 rewrite drop_app_length in HG.
  specialize (HG HG1 HG2). exact HG.
Qed.

Lemma Grel_downclosed :
  forall {m n : nat} {Hmn : m <= n} {Γ : nat} {Γ1 Γ2 : Env},
    Grel n Γ Γ1 Γ2 ->
    Grel m Γ Γ1 Γ2.
Proof.
  unfold Grel; intros. intuition.
  eapply Vrel_biforall_downclosed. eauto.
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

Theorem Vrel_VClos_compat_closed' :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + min (length Γ1) (length Γ2)) b1 b2 ->
    ENVCLOSED Γ1 -> ENVCLOSED Γ2 ->
    (*Grel m (length Γ1) Γ1 Γ2 ->*)
    Vrel_open (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
Proof.
  unfold Vrel_open. intros Γ1 Γ2 vl1 vl2 b1 b2 Hvl HE HEc1 HEc2 n. subst.
  revert Γ1 Γ2 vl2 b1 b2 HE HEc1 HEc2.
  induction n using Wf_nat.lt_wf_ind.
  intros Γ1 Γ2 vl2 b1 b2 HE HEc1 HEc2.
  rewrite Vrel_Fix_eq. simpl.
  split. 2:split.
  * constructor.
    + intros i Hi. apply ENVCLOSED_nth; auto.
    + apply Erel_open_scope_l in HE.
      eapply scope_ext_app. 2: eauto. lia.
  * constructor.
    + intros i Hi. apply ENVCLOSED_nth; auto.
    + apply Erel_open_scope_r in HE.
      eapply scope_ext_app. 2: eauto. lia.
  * rewrite Nat.eqb_refl.
  intros m Hm vals1 vals2 Hl1 Hl2 Hlbfa.
  epose proof (nH0 := HE m _ _ _).
  destruct nH0 as [nCl1 [nCl2 nH0]].
  split. exact nCl1.
  split. exact nCl2.
  intros m0 Hm0 F1 F2 HF D.
  eapply nH0. 3: exact D. lia. assumption.
Unshelve.
  simpl. apply Grel_cons.
  1: apply H; auto.
  apply Grel_app; auto.
  + unfold Grel. auto.
  + unfold Grel. split;[auto|].
Admitted.

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
    simpl. apply Grel_cons.
    apply H; auto. eapply Grel_downclosed; eauto.
    apply Grel_app; auto.
    unfold Grel; auto.
    eapply Grel_downclosed; eauto.
  Unshelve. lia. lia.
Qed.

Theorem Vrel_VClos_compat :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + length Γ1) b1 b2 ->
    (forall m, Grel m (length Γ1) Γ1 Γ2) ->
    (* ^^ is this correct??? *)
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
  apply Grel_length_eq in HG as HLeq.
  destruct HG as [Hl Hbfa].
  unfold exp_rel. split. 2: split.
  1,2: do 2 constructor; lia.
  intros m Hm F1 F2 HFR D.
  destruct HFR as [HF1 [HF2 HFR]].
  inv D.
  apply nth_lookup_Some with (d := VNil) in H1.
  apply indexed_to_biforall with (d1 := VNil) (d2 := VNil) in Hbfa.
  destruct Hbfa as [HG Hl].
  specialize (HG n H).
  rewrite H1 in HG.
  eapply step_terminates_one. constructor.
  2: eapply HFR.
  4: exact H4.
  2: lia.
  2: eapply Vrel_downclosed; exact HG.
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
  (*apply Grel_length_ge in HG as HG'.
  destruct HG' as [HG1 HG2].*)
  apply Grel_length_eq in HG as HG'.
  assert (length Γ1 = Γ) as HG1 by (destruct HG; lia).
  assert (length Γ2 = Γ) as HG2 by (destruct HG; lia).
  apply Erel_open_scope in He1 as He1sc.
  destruct He1sc as [He1sc He1'sc].
  apply Erel_open_scope in He2 as He2sc.
  destruct He2sc as [He2sc He2'sc].
  eapply Grel_closed in HG as HC.
  destruct HC as [HCΓ1 HCΓ2].
  split. 2: split.
  1-2: do 2 constructor.
  1-2: rewrite HG'.
  1-4: rewrite HG2; auto.
  intros m Hmn F1 F2 HF D.
  destruct HF as [HF1 [HF2 HF]].
  destruct m; inv D.
  unfold exp_rel in He2, He1.
  eapply He2 in H2 as [i D]; eauto.
  eexists. constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  1: rewrite HG2; auto.
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

Lemma Erel_EFun_compat :
  forall Γ (vl vl' : nat) b b',
    vl = vl' ->
    Erel_open (S vl + Γ) b b' ->
    Erel_open Γ (EFun vl b) (EFun vl' b').
Proof.
  intros Γ vl vl' b b' Hvl He. subst.
  unfold Erel_open. intros n Γ1 Γ2 HG.
  apply Grel_length_eq in HG as Heq.
  assert (length Γ1 = Γ) as HGeΓ1 by (destruct HG; lia).
  assert (length Γ2 = Γ) as HGeΓ2 by (destruct HG; lia).
  apply Grel_closed in HG as Hcl.
  destruct Hcl as [HclΓ1 HclΓ2].
  apply Erel_open_scope in He as Hesc.
  destruct Hesc as [Hbsc Hbsc'].
  split. 2: split.
  1-2: do 2 constructor.
  1: rewrite Heq.
  1-2: rewrite HGeΓ2; auto.
  intros m Hmn F1 F2 HF D.
  unfold frame_rel in HF.
  destruct m; inv D.
  eapply HF in H2 as [i D]; eauto.
  eexists. constructor. exact D.
  apply Vrel_VClos_compat_closed; auto.
  eapply Grel_downclosed. eauto.
  Unshelve. lia.
Qed.

Lemma Erel_ELet_compat :
  forall Γ e1 e1' e2 e2',
    Erel_open Γ e1 e1' ->
    Erel_open (S Γ) e2 e2' ->
    Erel_open Γ (ELet e1 e2) (ELet e1' e2').
Proof.
  intros Γ e1 e1' e2 e2' He1 He2.
  unfold Erel_open, exp_rel. intros n Γ1 Γ2 HG.
  apply Erel_open_scope in He1 as Hsc.
  destruct Hsc as [Hsce1 Hsce1'].
  apply Erel_open_scope in He2 as Hsc.
  destruct Hsc as [Hsce2 Hsce2'].
  apply Grel_length in HG as HGl.
  destruct HGl as [HGlΓ1 HGlΓ2].
  apply Grel_closed in HG as HC.
  destruct HC as [HCΓ1 HCΓ2].
  split. 2: split.
  1-2: try rewrite HGlΓ1; try rewrite HGlΓ2; do 2 constructor; auto.
  intros m Hmn F1 F2 [HF1 [HF2 HF]] D.
  inv D. eapply He1 in H4 as [i D]; eauto.
  exists (S i). constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto.
  1-2: constructor.
  4: rewrite HGlΓ2.
  1-4: auto.
  intros m Hmk v1 v2 Γ0 Γ3 HV D.
  inv D. eapply He2 in H8 as [i D]; eauto.
  exists (S i). constructor. exact D.
  apply Grel_cons. eapply Vrel_downclosed; eauto. eapply Grel_downclosed; eauto.
  split. 2: split. 1-2: auto.
  intros m Hmk0 v0 v3 Γ4 Γ5 HV' D.
  eapply HF in D as [i D]; eauto.
  exists i. exact D. lia.
  Unshelve. lia. lia.
Qed.

Lemma match_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  (forall l1, 
        (match_pattern p v1 = Some l1 ->
         exists l2, match_pattern p v2 = Some l2 /\ list_biforall (Vrel n) l1 l2)).
Proof.
  intros p v1 v2 n HV.
  apply Vrel_closed in HV as HVc. 
  destruct HVc as [HVc1 HVc2].
  generalize dependent v2. revert n. generalize dependent v1.
  induction p; intros v1 HVc1 n v2 HV HVc2 l1 Hm.
  1-5: destruct v1, v2; rewrite Vrel_Fix_eq in HV; simpl in HV; destruct HV as [Cl1 [Cl2 HV]];
       try contradiction; simpl in Hm; try discriminate; subst.
  * destruct (lit_eqb l2 l) eqn:Hl; try discriminate. inv Hm. exists []. simpl.
    apply lit_eqb_eq in Hl. subst. rewrite lit_eqb_refl. split. auto. constructor.
  * destruct (p1 =? p) eqn:Hp; try discriminate. inv Hm. rewrite Nat.eqb_eq in Hp. subst.
    exists []. simpl. rewrite Nat.eqb_refl. split. auto. constructor.
  * inv Hm. exists [VLit l0]. simpl. split. auto. constructor.
    apply Vrel_VLit_compat_closed. constructor.
  * inv Hm. exists [VPid p0]. split. auto. constructor. apply Vrel_VPid_compat_closed. constructor.
  * inv Hm. exists [VNil]. split. auto. constructor. apply Vrel_VNil_compat_closed. constructor.
  * destruct HV as [HV1 HV2]. rewrite <- Vrel_Fix_eq in HV1. rewrite <- Vrel_Fix_eq in HV2.
    inv Hm. eexists. split. auto. constructor. apply Vrel_VCons_compat_closed; auto. constructor.
  * inv Hm. eexists. split. auto. constructor. 2: constructor.
    rewrite Vrel_Fix_eq. simpl. auto.
  * inv Hm. exists []. split. auto. constructor.
  * destruct HV as [HV1 HV2]. rewrite <- Vrel_Fix_eq in HV1. rewrite <- Vrel_Fix_eq in HV2.
    inv Cl1. inv Cl2.
    destruct (match_pattern p1 v1_1) eqn:Hp1; try discriminate.
    destruct (match_pattern p2 v1_2) eqn:Hp2; try discriminate.
    eapply IHp1 in Hp1; eauto.
    eapply IHp2 in Hp2; eauto.
    destruct Hp1 as [l2 [Hmpl2 Hbfal2]].
    destruct Hp2 as [l2' [Hmpl2' Hbfal2']].
    eexists. split. simpl. rewrite Hmpl2. rewrite Hmpl2'. reflexivity.
    inv Hm. apply biforall_app; auto.
Qed.

Lemma nomatch_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  match_pattern p v1 = None -> match_pattern p v2 = None.
Proof.
  intros p v1 v2 n HV.
  apply Vrel_closed in HV as HVc.
  destruct HVc as [HVc1 HVc2].
  generalize dependent v2. revert n. generalize dependent v1.
  induction p; intros v1 HVc1 n v2 HV HVc2 Hm.
  all: destruct v1, v2; try reflexivity; simpl in Hm; try discriminate; rewrite Vrel_Fix_eq in HV;
       destruct HV as [CL1 [CL2 HV]]; try contradiction.
  * break_match_hyp; try discriminate. subst. simpl. rewrite Heqb. reflexivity.
  * break_match_hyp; try discriminate. subst. simpl. rewrite Heqb. reflexivity.
  * destruct HV as [HV1 HV2].
    rewrite <- Vrel_Fix_eq in HV1. rewrite <- Vrel_Fix_eq in HV2.
    inv CL1. inv CL2.
    destruct (match_pattern p1 v1_1) eqn:Hp1.
    + destruct (match_pattern p2 v1_2) eqn:Hp2; try discriminate.
      simpl. eapply IHp2 in Hp2; eauto. rewrite Hp2.
      destruct (match_pattern p1 v2_1); reflexivity.
    + simpl. eapply IHp1 in Hp1; eauto. rewrite Hp1. reflexivity.
Qed.

Lemma Erel_ECase_compat :
  forall Γ e1 e1' e2 e2' e3 e3' p,
    Erel_open Γ e1 e1' ->
    Erel_open (pat_vars p + Γ) e2 e2' ->
    Erel_open Γ e3 e3' ->
    Erel_open Γ (ECase e1 p e2 e3) (ECase e1' p e2' e3').
Proof.
  intros Γ e1 e1' e2 e2' e3 e3' p He1 He2 He3.
  unfold Erel_open, exp_rel. intros m Γ1 Γ2 HG.
  apply Grel_length in HG as Hl.
  destruct Hl as [HlΓ1 HlΓ2].
  apply Grel_closed in HG as Hc.
  destruct Hc as [HcΓ1 HcΓ2].
  apply Erel_open_scope in He1 as Hsce1.
  destruct Hsce1 as [Hsce1 Hsce1'].
  apply Erel_open_scope in He2 as Hsce2.
  destruct Hsce2 as [Hsce2 Hsce2'].
  apply Erel_open_scope in He3 as Hsce3.
  destruct Hsce3 as [Hsce3 Hsce3'].
  split. 2:split.
  1-2: try rewrite HlΓ1; try rewrite HlΓ2; do 2 constructor; auto.
  intros m0 Hm0n F1 F2 [HF1 [HF2 HF]] D.
  inv D. eapply He1 in H6 as [i D]; eauto.
  exists (S i). constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  1-2: rewrite HlΓ2; auto.
  intros m0 Hm0k v1 v2 Γ0 Γ3 HV D.
  inv D.
  * apply match_pattern_Vrel with (p := p) (l1 := l) in HV as Hmp; auto.
    destruct Hmp as [l2 [Hmp Hmpbfa]].
    eapply He2 in H11 as [i D]; eauto.
    exists (S i). eapply term_case_true; eauto.
    apply match_pattern_length in H10.
    apply match_pattern_length in Hmp.
    apply Grel_app; auto.
    unfold Grel. split. auto. eapply Vrel_biforall_downclosed. eauto.
    eapply Grel_downclosed. eauto.
    split. 2: split. 1-2: auto.
    intros m0 Hm0k0 v0 v3 Γ4 Γ5 HV' D.
    eapply HF in D as [i D]; eauto.
    exists i. exact D. lia.
    Unshelve. lia. lia.
  * apply nomatch_pattern_Vrel with (p := p) in HV as Hmp; auto.
    eapply He3 in H11 as [i D]; eauto.
    exists (S i). eapply term_case_false; eauto. lia.
    split. 2: split. 1-2: auto.
    intros m0 Hm0k0 v0 v3 Γ4 Γ5 HV' D.
    eapply HF in D as [i D]; eauto.
    exists i. exact D. lia.
Qed.



























