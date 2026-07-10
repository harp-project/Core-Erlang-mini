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
      vl1 = vl2 /\
      forall m (Hmn : m < n), forall (vals1 vals2 : list Val),
        length vals1 = vl1 -> length vals2 = vl2 ->
        list_biforall (Vrel m Hmn) vals1 vals2
      ->
        exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
          (VClos Γ1 vl1 b1 :: vals1 ++ Γ1) (VClos Γ2 vl2 b2 :: vals2 ++ Γ2) b1 b2
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

Definition Vrel_all (v1 v2 : Val) : Prop :=
  forall n,
    Vrel n v1 v2.
(* Actually it does make sense to have an "open" Vrel. For this definition, n is bound in a
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
  * f_equal. f_equal. f_equal.
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
    intuition.
    apply H3; auto. lia.
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

Lemma exp_rel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Exp} {Γ1 Γ2 : Env},
    exp_rel n (fun m _ => Vrel m) Γ1 Γ2 e1 e2 -> 
    exp_rel m (fun m _ => Vrel m) Γ1 Γ2 e1 e2.
Proof.
  intros. unfold exp_rel in *.
  destruct H as [Hs1 [Hs2 H]].
  split. 2:split. 1-2: auto.
  intros. eapply H. 3: exact H1. lia. exact H0.
Qed.

Lemma exp_rel_biforall_downclosed :
  forall {n m : nat} {Hmn : m <= n} {l1 l2 : list Exp} {Γ1 Γ2 : Env},
    list_biforall (exp_rel n (fun m _ => Vrel m) Γ1 Γ2) l1 l2 ->
    list_biforall (exp_rel m (fun m _ => Vrel m) Γ1 Γ2) l1 l2.
Proof.
  intros n m Hmn l1.
  induction l1; intros l2 Γ1 Γ2 HE.
  * inv HE. constructor.
  * inv HE. constructor.
    + eapply exp_rel_downclosed. eauto. Unshelve. lia.
    + auto.
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

Corollary Vrel_biforall_closed :
  forall m l1 l2,
    list_biforall (Vrel m) l1 l2 ->
      Forall (fun w => VALCLOSED w) l1 /\
      Forall (fun w => VALCLOSED w) l2.
Proof.
  intros m l1. induction l1; intros l2 Hbfa.
  * destruct l2; inv Hbfa. repeat constructor.
  * destruct l2; inv Hbfa. apply Vrel_closed in H2 as [Hc1 Hc2].
    specialize (IHl1 l2 H4) as [Fl1 Fl2].
    repeat constructor; auto.
Qed.

Corollary Vrel_biforall_closed_l :
  forall m l1 l2,
    list_biforall (Vrel m) l1 l2 ->
      Forall (fun w => VALCLOSED w) l1.
Proof. apply Vrel_biforall_closed. Qed.

Corollary Vrel_biforall_closed_r :
  forall m l1 l2,
    list_biforall (Vrel m) l1 l2 ->
      Forall (fun w => VALCLOSED w) l2.
Proof. apply Vrel_biforall_closed. Qed.

Lemma exp_rel_scope :
  forall m H Γ1 Γ2 e1 e2,
    exp_rel m H Γ1 Γ2 e1 e2 ->
    EXP length Γ1 ⊢ e1 /\ EXP length Γ2 ⊢ e2.
Proof. intros. split; apply H0. Qed.

Corollary exp_rel_scope_l :
  forall m H Γ1 Γ2 e1 e2,
    exp_rel m H Γ1 Γ2 e1 e2 ->
    EXP length Γ1 ⊢ e1.
Proof. apply exp_rel_scope. Qed.

Corollary exp_rel_scope_r :
  forall m H Γ1 Γ2 e1 e2,
    exp_rel m H Γ1 Γ2 e1 e2 ->
    EXP length Γ2 ⊢ e2.
Proof. apply exp_rel_scope. Qed.

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
    Grel m Γ Γ1 Γ2 ->
    Grel m Γ' Γ1' Γ2' ->
    Grel m (Γ + Γ') (Γ1 ++ Γ1') (Γ2 ++ Γ2').
Proof.
  intros m Γ Γ' Γ1 Γ1' Γ2 Γ2' HG1 HG2.
  pose proof (Grel_length_l _ _ _ _ HG1) as HΓ1.
  pose proof (Grel_length_r _ _ _ _ HG1) as HΓ2.
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
    Vrel_all (VLit l) (VLit l).
Proof.
  unfold Vrel_all. intros. apply Vrel_VLit_compat_closed.
Qed.

Theorem Vrel_VPid_compat_closed :
  forall m p,
    Vrel m (VPid p) (VPid p).
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. auto.
Qed.

Theorem Vrel_VPid_compat :
  forall p,
    Vrel_all (VPid p) (VPid p).
Proof.
  unfold Vrel_all. intros. apply Vrel_VPid_compat_closed.
Qed.

Theorem Vrel_VNil_compat_closed :
  forall m,
    Vrel m VNil VNil.
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. auto.
Qed.

Theorem Vrel_VNil_compat :
  Vrel_all VNil VNil.
Proof.
  unfold Vrel_all. intros. apply Vrel_VNil_compat_closed.
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
    Vrel_all hd hd' -> Vrel_all tl tl' ->
    Vrel_all (VCons hd tl) (VCons hd' tl').
Proof.
  unfold Vrel_all. intros. apply Vrel_VCons_compat_closed; auto.
Qed.

(* Theorem Vrel_VClos_compat_closed' :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + min (length Γ1) (length Γ2)) b1 b2 ->
    ENVCLOSED Γ1 -> ENVCLOSED Γ2 ->
    (*Grel m (length Γ1) Γ1 Γ2 ->*)
    Vrel_all (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
Proof.
  unfold Vrel_all. intros Γ1 Γ2 vl1 vl2 b1 b2 Hvl HE HEc1 HEc2 n. subst.
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
  epose proof (nH0 := HE m _ _ _). (* This is where Grel goes to the shelf *)
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
Admitted. *)

(* 

Lemma Vrel_Clos_compat :
  forall Γ ext1 ext2 id1 id2 vl1 vl2 b1 b2,
  vl1 = vl2 ->
  Erel_open (length ext1 + vl1 + Γ) b1 b2 ->
  Vrel_all Γ (VClos vl1 b1) (VClos vl2 b2).

 *)


Theorem Vrel_VClos_compat :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + length Γ1) b1 b2 ->
    forall m, 
      Grel m (length Γ1) Γ1 Γ2 ->
      Vrel m (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
      (* ^^^ This is the same as Vrel_Clos_compat in the subst-semantics, but in that
             lemma Vrel_all is used. In the subst version, 2 values are related under
             Vrel_all if for related substitutions the values are related under Vrel.
             
             In the env-semantics the closure stores the environment that the function
             was evaluated in, because it will be needed for the beta reduction. We can
             think of the stored environment as the values that have aready been
             substituted. This is part of the reason why it doesn't make sense to put a
             Grel inside Vrel_all in this version.
             
             Recall the relevant part from Vrel_rec in the subst and env semantics:
                
                 "exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                            (b1.[list_subst (EFun vl1 b1 :: vals1) idsubst])
                            (b2.[list_subst (EFun vl2 b2 :: vals2) idsubst])"
                 
                 "exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                            (VClos Γ1 vl1 b1 :: vals1 ++ Γ1)
                            (VClos Γ2 vl2 b2 :: vals2 ++ Γ2) b1 b2"
             
             Since Γ1 and Γ2 contain the values aready substituted, the variables to these
             bindings don't exist in the substitution version. But with Vrel_all, the
             variables are still present, and related variables need to be substituted in.
             That is why Grel is used in the subst-semantics version of Vrel_all.
             
             But in the env-semantics, we also need the stored environments to be related.
             This is because even though values do not depend on the environment, expressions
             do, and closures are only equivalent if their stored expressions are equivalent
             under the right environment. That environment depends on the environment that
             was used when the closure was created.
             
             All in all, this lemma looks different from the substitution-version, but the
             last 3 lines are the subst-semantics version of Vrel_all unfolded.
      *)
Proof.
  intros * Hl HE m. revert Γ1 Γ2 vl1 vl2 b1 b2 Hl HE.
  induction m using Wf_nat.lt_wf_ind.
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
  * split;[auto|].
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

(* Theorem Vrel_VClos_compat :
  forall Γ1 Γ2 vl1 vl2 b1 b2,
    vl1 = vl2 ->
    Erel_open (S vl1 + length Γ1) b1 b2 ->
    (forall m, Grel m (length Γ1) Γ1 Γ2) ->
    (* ^^ is this correct??? *)
    Vrel_all (VClos Γ1 vl1 b1) (VClos Γ2 vl2 b2).
Proof.
  unfold Vrel_all. intros. apply Vrel_VClos_compat_closed; auto.
Qed. *)

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
    Vrel_all v1 v2 ->
    Erel_open Γ (˝v1) (˝v2).
Proof.
  unfold Vrel_all, Erel_open. intros.
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
  apply Vrel_VClos_compat; auto.
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

Lemma Erel_open_biforall_scope :
  forall Γ vals1 vals2 i def,
    i < length vals1 ->
    list_biforall (Erel_open Γ) vals1 vals2 ->
    EXP Γ ⊢ nth i vals1 def /\ EXP Γ ⊢ nth i vals2 def.
Proof.
  intros Γ vals1 vals2 i def Hi Hbfa.
  apply indexed_to_biforall with (d1 := def) (d2 := def) in Hbfa.
  destruct Hbfa as [Hnth Hl].
  specialize (Hnth i Hi).
  apply Erel_open_scope in Hnth. auto.
Qed.

Corollary Erel_open_biforall_scope_l :
  forall Γ vals1 vals2 i def,
    i < length vals1 ->
    list_biforall (Erel_open Γ) vals1 vals2 ->
    EXP Γ ⊢ nth i vals1 def.
Proof. apply Erel_open_biforall_scope. Qed.

Corollary Erel_open_biforall_scope_r :
  forall Γ vals1 vals2 i def,
    i < length vals1 ->
    list_biforall (Erel_open Γ) vals1 vals2 ->
    EXP Γ ⊢ nth i vals2 def.
Proof. apply Erel_open_biforall_scope. Qed.

Lemma Erel_open_biforall_Forall_scope :
  forall Γ vals1 vals2,
    list_biforall (Erel_open Γ) vals1 vals2 ->
    Forall (fun e => EXP Γ ⊢ e) vals1 /\ Forall (fun e => EXP Γ ⊢ e) vals2.
Proof.
  intros Γ vals1.
  induction vals1; intros vals2 Hbfa.
  * destruct vals2; inv Hbfa. split; constructor.
  * destruct vals2; inv Hbfa. apply IHvals1 in H4 as [HF1 HF2].
    apply Erel_open_scope in H2 as [HS1 HS2].
    split; constructor; auto.
Qed.

Corollary Erel_open_biforall_Forall_scope_l :
  forall Γ vals1 vals2,
    list_biforall (Erel_open Γ) vals1 vals2 ->
    Forall (fun e => EXP Γ ⊢ e) vals1.
Proof. apply Erel_open_biforall_Forall_scope. Qed.

Corollary Erel_open_biforall_Forall_scope_r :
  forall Γ vals1 vals2,
    list_biforall (Erel_open Γ) vals1 vals2 ->
    Forall (fun e => EXP Γ ⊢ e) vals2.
Proof. apply Erel_open_biforall_Forall_scope. Qed.

Lemma exp_rel_biforall_Forall_scope :
  forall m H Γ1 Γ2 l1 l2,
    list_biforall (exp_rel m H Γ1 Γ2) l1 l2 ->
    Forall (fun e => EXP length Γ1 ⊢ e) l1 /\ Forall (fun e => EXP length Γ2 ⊢ e) l2.
Proof.
  intros m H Γ1 Γ2 l1.
  induction l1; intros l2 Hbfa.
  * destruct l2; inv Hbfa. split; constructor.
  * destruct l2; inv Hbfa. apply IHl1 in H5 as [HF1 HF2].
    apply exp_rel_scope in H3 as [H3 H3'].
    split; constructor; auto.
Qed.

Corollary exp_rel_biforall_Forall_scope_l:
  forall m H Γ1 Γ2 l1 l2,
    list_biforall (exp_rel m H Γ1 Γ2) l1 l2 ->
    Forall (fun e => EXP length Γ1 ⊢ e) l1.
Proof. apply exp_rel_biforall_Forall_scope. Qed.

Corollary exp_rel_biforall_Forall_scope_r:
  forall m H Γ1 Γ2 l1 l2,
    list_biforall (exp_rel m H Γ1 Γ2) l1 l2 ->
    Forall (fun e => EXP length Γ2 ⊢ e) l2.
Proof. apply exp_rel_biforall_Forall_scope. Qed.

Lemma Erel_EApp_compat_ind : forall hds hds' tl tl' F1 F2 k0 (v1 v2 : Val) (Γ1 Γ2 : Env),
  list_biforall (exp_rel k0 (fun m _ => Vrel m) Γ1 Γ2) hds hds' ->
  list_biforall (Vrel k0) tl tl' ->
  Vrel k0 v1 v2 ->
  FSCLOSED F1 ->
  FSCLOSED F2 ->
  ENVCLOSED Γ1 ->
  ENVCLOSED Γ2 ->
  (forall m : nat, m <= k0 -> forall (v1 v2 : Val) (Γ1 Γ2 : Env),
      Vrel m v1 v2 -> | Γ1, F1, v1 | m ↓ -> | Γ2, F2, v2 | ↓)
->
  frame_rel k0 (fun (m' : nat) (_ : m' <= k0) => Vrel m') (FApp2 v1 tl hds Γ1 :: F1)
  (FApp2 v2 tl' hds' Γ2 :: F2).
Proof.
  induction hds; intros * Hhds Htl Hv HF1 HF2 HΓ1 HΓ2 HF.
  * inv Hhds. apply biforall_length in Htl as Hl.
    apply Vrel_biforall_closed in Htl as Htlc. destruct Htlc as [Htlc Htl'c].
    apply Vrel_closed in Hv as Hvc. destruct Hvc as [Hv1c Hv2c].
    split. 2: split. 1-2: constructor; auto; constructor; auto.
    intros m Hmk0 v0 v3 Γ0 Γ3 HV' D.
    inv D.
    destruct v1; try discriminate. simpl in H6.
    destruct (length (tl ++ [v0]) =? vl) eqn:Htlvl; try discriminate.
    inv H6. apply Nat.eqb_eq in Htlvl.
    rewrite Vrel_Fix_eq in Hv. destruct Hv as [Hvc1 [Hvc2 Hv]].
    destruct v2; try contradiction.
    destruct Hv as [Hvlvl0 Hv]. subst.
    eapply step_terminates_one.
    constructor. simpl. do 2 rewrite length_app. rewrite <- Hl. simpl.
    rewrite Nat.eqb_refl. reflexivity. rewrite length_app in H7. simpl in H7.
    rewrite length_app in Hv. simpl in Hv.
    eapply Hv; eauto.
    1-2: rewrite length_app.
    2: rewrite Hl.
    1-2: reflexivity.
    1: { apply biforall_app.
         * eapply Vrel_biforall_downclosed; eauto.
         * constructor;[|constructor]. eapply Vrel_downclosed; eauto. }
    split. 2: split. 1-2: auto.
    intros m Hmk v1 v2 Γ5 Γ6 HV'' D. eapply HF in D. exact D. lia. exact HV''.
  * inv Hhds. apply biforall_length in Htl as Hl.
    apply Vrel_biforall_closed in Htl as Htlc. destruct Htlc as [Htlc Htl'c].
    apply exp_rel_biforall_Forall_scope in H3 as Hhdc. destruct Hhdc as [Hhdc Hhd'c].
    apply Vrel_closed in Hv as Hvc. destruct Hvc as [Hv1c Hv2c].
    apply exp_rel_scope in H1 as Hes. destruct Hes as [Has Hhd's].
    split. 2: split. 1-2: constructor; auto; constructor; auto; constructor; auto.
    intros m Hmk0 v0 v3 Γ0 Γ3 HV' D.
    inv D. eapply step_terminates_one. constructor.
    eapply H1. 3: exact H10. 1: lia.
    eapply IHhds; auto.
    + eapply exp_rel_biforall_downclosed. eauto.
    + apply biforall_app. eapply Vrel_biforall_downclosed. eauto.
      constructor;[|constructor]. eapply Vrel_downclosed. eauto.
    + eapply Vrel_downclosed. eauto.
    + intros m Hmk v4 v5 Γ4 Γ5 HV'' D. eapply HF. 2: exact HV''. 2: exact D. lia.
Unshelve. all:lia.
Qed.

Lemma Erel_EApp_compat_helper : forall es es' k F1 F2 Γ1 Γ2 (FCL1 : FSCLOSED F1) (FCL2 : FSCLOSED F2) (ΓCL1 : ENVCLOSED Γ1) (ΓCL2 : ENVCLOSED Γ2),
  (forall m : nat, m <= S k -> forall (v1 v2 : Val) (Γ1 Γ2 : Env), 
      Vrel m v1 v2 -> | Γ1, F1, v1 | m ↓ -> | Γ2, F2, v2 | ↓) ->
  list_biforall (exp_rel k (fun m _ => Vrel m) Γ1 Γ2) es es' ->
  forall m, m <= k -> 
  forall (v1 v2 : Val) (Γ3 Γ4 : Env), 
      Vrel m v1 v2 -> | Γ3, FApp1 es Γ1 :: F1, v1 | m ↓ -> | Γ4, FApp1 es' Γ2 :: F2, v2 | ↓.
Proof.
  destruct es; intros * FCL1 FCL2 ΓCL1 ΓCL2 HF Hes m Hmk v1 v2 Γ3 Γ4 HV D.
  * inv Hes. inv D. destruct v1; try discriminate. simpl in H3.
    destruct vl; try discriminate. inv H3.
    rewrite Vrel_Fix_eq in HV. destruct HV as [HVc1 [HVc2 HV]].
    destruct v2; try contradiction.
    destruct HV as [Hl HV]. subst vl.
    eapply step_terminates_one. constructor. reflexivity. simpl.
    assert ((VClos Γ0 0 e :: Γ0) = (VClos Γ0 0 e :: [] ++ Γ0)) by reflexivity.
    rewrite H. clear H.
    assert ((VClos Γ 0 res :: Γ) = (VClos Γ 0 res :: [] ++ Γ)) by reflexivity.
    rewrite H in H5. clear H.
    eapply HV; eauto. reflexivity. constructor.
    split. 2: split. 1-2: auto.
    intros m Hmk0 v1 v2 Γ5 Γ6 HV' D.
    eapply HF. 2: exact HV'. 2: exact D. lia.
  * inv Hes. inv D. eapply step_terminates_one. constructor.
    destruct H1 as [Hes1 [Hes2 He]].
    eapply He. 3: exact H8. lia.
    apply Erel_EApp_compat_ind; auto.
    + eapply exp_rel_biforall_downclosed. eauto.
    + constructor.
    + eapply Vrel_downclosed. eauto.
    + intros m Hmk0 v0 v3 Γ0 Γ HV' D.
      eapply HF. 2: exact HV'. 2: exact D. lia.
Unshelve. lia. lia.
Qed.

Lemma Erel_EApp_compat :
  forall Γ f1 f2 vals1 vals2,
    Erel_open Γ f1 f2 ->
    list_biforall (Erel_open Γ) vals1 vals2 ->
    Erel_open Γ (EApp f1 vals1) (EApp f2 vals2).
Proof.
  intros Γ f1 f2 vals1 vals2 Hf Hvals.
  unfold Erel_open. intros n Γ1 Γ2 HG.
  apply Erel_open_scope in Hf as Hs.
  destruct Hs as [Hsf1 Hsf2].
  apply Grel_closed in HG as HC.
  destruct HC as [HCΓ1 HCΓ2].
  apply Grel_length in HG as HL.
  destruct HL as [HLΓ1 HLΓ2].
  apply biforall_length in Hvals as Hlen.
  split. 2: split.
  1-2: do 2 constructor.
  1,3: try rewrite HLΓ1; try rewrite HLΓ2; auto.
  1-2: intros i Hi; try rewrite HLΓ1; try rewrite HLΓ2.
  1-2: pose proof (Erel_open_biforall_scope).
  eapply Erel_open_biforall_scope_l; eauto.
  rewrite <- Hlen in Hi.
  eapply Erel_open_biforall_scope_r; eauto.
  intros m Hmn F1 F2 [HF1 [HF2 HF]] D.
  inv D. eapply Hf in H4 as [i D]; eauto.
  exists (S i). constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  1-2: apply Erel_open_biforall_Forall_scope in Hvals as [Hvals1 Hvals2].
  2: rewrite HLΓ2.
  1-2: auto.
  intros m Hmk v1 v2 Γ0 Γ3 HV D.
  
  eapply Erel_EApp_compat_helper in D. exact D. all: auto.
  intros m0 Hm0m v0 v3 Γ4 Γ5 HV' D'. eapply HF in D'; eauto. lia.
  clear -HG Hvals Hmk Hmn.
  generalize dependent vals2.
  induction vals1; intros vals2 Hvals.
  * inv Hvals. constructor.
  * inv Hvals. apply IHvals1 in H3.
    constructor; auto. apply H1.
    eapply Grel_downclosed. eauto.
Unshelve. lia.
Qed.

Lemma Erel_EBIF_compat_ind : forall hds hds' tl tl' F1 F2 k0 (v1 v2 : Val) (Γ1 Γ2 : Env),
  list_biforall (exp_rel k0 (fun m _ => Vrel m) Γ1 Γ2) hds hds' ->
  list_biforall (Vrel k0) tl tl' ->
  Vrel k0 v1 v2 ->
  FSCLOSED F1 ->
  FSCLOSED F2 ->
  ENVCLOSED Γ1 ->
  ENVCLOSED Γ2 ->
  (forall m : nat, m <= k0 -> forall (v1 v2 : Val) (Γ1 Γ2 : Env),
      Vrel m v1 v2 -> | Γ1, F1, v1 | m ↓ -> | Γ2, F2, v2 | ↓)
->
  frame_rel k0 (fun (m' : nat) (_ : m' <= k0) => Vrel m') (FBIF2 v1 tl hds Γ1 :: F1)
  (FBIF2 v2 tl' hds' Γ2 :: F2).
Proof.
  induction hds; intros * Hhds Htl Hv HF1 HF2 HΓ1 HΓ2 HF.
  * inv Hhds. apply biforall_length in Htl as Hl.
    apply Vrel_biforall_closed in Htl as Htlc. destruct Htlc as [Htlc Htl'c].
    apply Vrel_closed in Hv as Hvc. destruct Hvc as [Hv1c Hv2c].
    split. 2: split. 1-2: constructor; auto; constructor; auto.
    intros m Hmk0 v0 v3 Γ0 Γ3 HV' D.
    inv D.
    destruct v1; try discriminate. simpl in H6.
    destruct l; try discriminate.
    destruct s; try discriminate.
    destruct a; try discriminate.
    destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
    destruct s; try discriminate.
    destruct tl.
    1: { simpl in H6. destruct v0; try discriminate. destruct l; try discriminate. }
    simpl in H6.
    destruct v; try discriminate.
    destruct l; try discriminate.
    destruct tl.
    2: { simpl in H6. destruct v; try discriminate. destruct l; try discriminate.
         destruct tl; discriminate. }
    simpl in H6.
    destruct v0; try discriminate.
    destruct l; try discriminate. inv H6.
    rewrite Vrel_Fix_eq in Hv. simpl in Hv. destruct Hv as [Hvc1 [Hvc2 Hv]].
    destruct v2; try contradiction. subst.
    inv Htl'c. inv Htl. rewrite Vrel_Fix_eq in H4. simpl in H4.
    destruct H4 as [_ [_ H4]]. destruct x; try contradiction. subst.
    inv H6.
    rewrite Vrel_Fix_eq in HV'. destruct HV' as [_ [_ HV']].
    destruct v3; try contradiction. subst.
    eapply step_terminates_one. constructor. reflexivity.
    eapply HF in H7. exact H7. lia. apply Vrel_VLit_compat.
  * inv Hhds. apply biforall_length in Htl as Hl.
    apply Vrel_biforall_closed in Htl as Htlc. destruct Htlc as [Htlc Htl'c].
    apply exp_rel_biforall_Forall_scope in H3 as Hhdc. destruct Hhdc as [Hhdc Hhd'c].
    apply Vrel_closed in Hv as Hvc. destruct Hvc as [Hv1c Hv2c].
    apply exp_rel_scope in H1 as Hes. destruct Hes as [Has Hhd's].
    split. 2: split. 1-2: constructor; auto; constructor; auto; constructor; auto.
    intros m Hmk0 v0 v3 Γ0 Γ3 HV' D.
    inv D. eapply step_terminates_one. constructor.
    eapply H1. 3: exact H10. 1: lia.
    eapply IHhds; auto.
    + eapply exp_rel_biforall_downclosed. eauto.
    + apply biforall_app. eapply Vrel_biforall_downclosed. eauto.
      constructor;[|constructor]. eapply Vrel_downclosed. eauto.
    + eapply Vrel_downclosed. eauto.
    + intros m Hmk v4 v5 Γ4 Γ5 HV'' D. eapply HF. 2: exact HV''. 2: exact D. lia.
Unshelve. all:lia.
Qed.

Lemma Erel_EBIF_compat_helper : forall es es' k F1 F2 Γ1 Γ2 (FCL1 : FSCLOSED F1) (FCL2 : FSCLOSED F2) (ΓCL1 : ENVCLOSED Γ1) (ΓCL2 : ENVCLOSED Γ2),
  (forall m : nat, m <= S k -> forall (v1 v2 : Val) (Γ1 Γ2 : Env), 
      Vrel m v1 v2 -> | Γ1, F1, v1 | m ↓ -> | Γ2, F2, v2 | ↓) ->
  list_biforall (exp_rel k (fun m _ => Vrel m) Γ1 Γ2) es es' ->
  forall m, m <= k -> 
  forall (v1 v2 : Val) (Γ3 Γ4 : Env), 
      Vrel m v1 v2 -> | Γ3, FBIF1 es Γ1 :: F1, v1 | m ↓ -> | Γ4, FBIF1 es' Γ2 :: F2, v2 | ↓.
Proof.
  destruct es; intros * FCL1 FCL2 ΓCL1 ΓCL2 HF Hes m Hmk v1 v2 Γ3 Γ4 HV D.
  * inv Hes. inv D. destruct v1; try discriminate. simpl in H3.
    destruct l; try discriminate.
    destruct s; try discriminate.
    destruct a; try discriminate.
    destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
    destruct s; try discriminate.
  * inv Hes. inv D. eapply step_terminates_one. constructor.
    destruct H1 as [Hes1 [Hes2 He]].
    eapply He. 3: exact H8. lia.
    apply Erel_EBIF_compat_ind; auto.
    + eapply exp_rel_biforall_downclosed. eauto.
    + constructor.
    + eapply Vrel_downclosed. eauto.
    + intros m Hmk0 v0 v3 Γ0 Γ HV' D.
      eapply HF. 2: exact HV'. 2: exact D. lia.
Unshelve. lia. lia.
Qed.

Lemma Erel_EBIF_compat :
  forall Γ f1 f2 vals1 vals2,
    Erel_open Γ f1 f2 ->
    list_biforall (Erel_open Γ) vals1 vals2 ->
    Erel_open Γ (EBIF f1 vals1) (EBIF f2 vals2).
Proof.
  intros Γ f1 f2 vals1 vals2 Hf Hbfa n Γ1 Γ2 HG.
  apply Erel_open_scope in Hf as Hfs. destruct Hfs as [Hf1s Hf2s].
  apply Erel_open_biforall_Forall_scope in Hbfa as Hbfas.
  destruct Hbfas as [Hbfas1 Hbfas2].
  apply Grel_length in HG as HGl. destruct HGl as [HGl1 HGl2].
  apply Grel_closed in HG as HGc. destruct HGc as [HGc1 HGc2].
  split. 2: split.
  1-2: do 2 constructor; try rewrite HGl1; try rewrite HGl2; auto.
  1-2: intros i Hi; eapply Erel_open_biforall_scope with (i := i) 
                    in Hbfa as [Hbfa1 Hbfa2]; eauto.
  1: apply biforall_length in Hbfa. lia.
  intros m Hmn F1 F2 [HF1 [HF2 HF]] D.
  inv D. eapply Hf in H4 as [i D]; eauto.
  exists (S i). constructor. exact D. lia.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  1: rewrite HGl2; auto.
  intros m Hmk v1 v2 Γ0 Γ3 HV D.
  
  eapply Erel_EBIF_compat_helper in D. exact D. all: auto.
  intros m0 Hm0m v0 v3 Γ4 Γ5 HV' D'.
  eapply HF in D'. exact D'. lia. exact HV'.
  clear -HG Hbfa Hmk Hmn.
  generalize dependent vals2.
  induction vals1; intros vals2 Hbfa.
  * inv Hbfa. constructor.
  * inv Hbfa. apply IHvals1 in H3. constructor; auto.
    apply H1. eapply Grel_downclosed. eauto.
Unshelve. lia.
Qed.

Theorem Erel_Fundamental :
  forall (e : Exp) (Γ : nat),
    EXP Γ ⊢ e -> Erel_open Γ e e.
Proof.
  intros e.
  induction e using Exp_ind2 with
  (PN := fun n => forall Γ, NVAL Γ ⊢ n -> Erel_open Γ n n)
  (PV := fun v => VALCLOSED v -> Vrel_all v v)
  (Q  := Forall (fun e => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e))
  (R  := Forall (fun v => VALCLOSED v -> Vrel_all v v)); intros; auto.
  * apply IHe. inv H. auto.
  * apply Erel_Val_compat. apply IHe. inv H. auto.
  * inv H. apply Erel_EFun_compat; auto.
  * inv H. apply Erel_EApp_compat.
    + apply IHe. exact H2.
    + apply forall_biforall_refl.
      induction IHe0. constructor.
      constructor. apply H. specialize (H4 0 (Nat.lt_0_succ _)). simpl in H4. auto.
      apply IHIHe0. intros. apply (H4 (S i)). simpl. lia.
  * inv H. apply Erel_ELet_compat; auto.
  * inv H. apply Erel_ECase_compat. all:auto.
  * inv H. apply Erel_ECons_compat; auto.
  * inv H. apply Erel_EBIF_compat; auto.
    apply forall_biforall_refl.
    induction IHe0. constructor.
    constructor. specialize (H4 0 (Nat.lt_0_succ _)). simpl in H4. auto.
    apply IHIHe0. intros. apply (H4 (S i)). simpl. lia.
  * inv H. apply Erel_EVar_compat. auto.
  * apply Vrel_VLit_compat.
  * apply Vrel_VPid_compat.
  * apply Vrel_VNil_compat.
  * inv H. apply Vrel_VCons_compat; auto.
  * inv H. intros n. apply Vrel_VClos_compat; auto.
    unfold Grel. split; auto.
    apply forall_biforall_refl.
    clear H4 IHe0.
    induction IHe. constructor.
    constructor. specialize (H2 0 (Nat.lt_0_succ _)). simpl in H2.
    apply H in H2. auto.
    apply IHIHe. intros. apply (H2 (S i)). simpl. lia.
Qed.

Theorem Vrel_Fundamental :
  forall (v : Val),
    VALCLOSED v -> Vrel_all v v.
Proof.
  intros v.
  induction v using Val_ind2 with
  (P  := fun e => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e)
  (PN := fun n => forall Γ, NVAL Γ ⊢ n -> Erel_open Γ n n)
  (Q  := Forall (fun e => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e))
  (R  := Forall (fun v => VALCLOSED v -> Vrel_all v v));
      intros; auto; try (apply Erel_Fundamental; auto).
  * apply Vrel_VLit_compat.
  * apply Vrel_VPid_compat.
  * apply Vrel_VNil_compat.
  * inv H. apply Vrel_VCons_compat; auto.
  * inv H. intros n. apply Vrel_VClos_compat; auto.
    unfold Grel. split; auto.
    clear IHv0 H4.
    apply forall_biforall_refl. induction IHv. constructor.
    constructor. specialize (H2 0 (Nat.lt_0_succ _)). simpl in H2.
    apply H in H2. auto.
    apply IHIHv. intros. apply (H2 (S i)). simpl. lia.
Qed.

Corollary Vrel_Fundamental_closed :
  forall (v : Val),
    VALCLOSED v -> forall n, Vrel n v v.
Proof. apply Vrel_Fundamental. Qed.

Theorem Grel_Fundamental :
  forall (G : Env) (Γ : nat),
    ENVCLOSED G -> length G = Γ -> 
      forall n, Grel n Γ G G.
Proof.
  intros. unfold Grel. split; auto.
  clear Γ H0. apply forall_biforall_refl.
  induction G. constructor.
  inv H. apply IHG in H3. constructor; auto.
  apply Vrel_Fundamental_closed. auto.
Qed.

Lemma Vrel_all_closed :
  forall {v v'},
    Vrel_all v v' -> VALCLOSED v /\ VALCLOSED v'.
Proof.
  (* Since Vrel_all doesn't contain Grel, this is much easier than the subst version. *)
  intros. specialize (H 42). apply Vrel_closed in H. auto.
Qed.

Lemma Frel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    Frel m F1 F2.
Proof.
  intros n m Hmn F1 F2 HF.
  repeat split; try apply HF.
  intros m0 Hm0m v1 v2 Γ1 Γ2 Hv D.
  destruct HF as [_ [_ HF]].
  eapply HF in D as [i D]; eauto.
  exists i. eauto. lia.
Qed.

Lemma Frel_closed :
  forall n F1 F2,
    Frel n F1 F2 -> FSCLOSED F1 /\ FSCLOSED F2.
Proof. intros. split; apply H. Qed.

Corollary Frel_closed_l :
  forall n F1 F2,
    Frel n F1 F2 -> FSCLOSED F1.
Proof. apply Frel_closed. Qed.

Corollary Frel_closed_r :
  forall n F1 F2,
    Frel n F1 F2 -> FSCLOSED F2.
Proof. apply Frel_closed. Qed.

Lemma Frel_FLet :
  forall n e2 e2' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (forall m v1 v1',
    m <= n -> Vrel m v1 v1' -> exp_rel m (fun m _ => Vrel m) (v1 :: Γ) (v1' :: Γ') e2 e2') ->
  forall m F1 F2, m <= n -> Frel m F1 F2 ->
    Frel m (FLet e2 Γ :: F1) (FLet e2' Γ' :: F2).
Proof.
  intros n e2 e2' Γ Γ' HGc1 HGc2 Hv m F1 F2 Hmn HF.
  specialize (Hv m VNil VNil Hmn (Vrel_VNil_compat _)) as Hvs.
  apply Frel_closed in HF as HFc. destruct HFc as [HFc1 HFc2].
  destruct Hvs as [He2s [He2's Hvs]]. simpl in He2s, He2's.
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v2 Γ1 Γ2 HV D.
  inv D. eapply Hv in H5 as [i D].
  exists (S i). constructor. exact D.
  2: exact HV. 1-2: lia.
  split. 2: split. 1-2: auto.
  eapply Frel_downclosed. eauto.
  Unshelve. lia.
Qed.

Lemma Frel_FCons1 :
  forall n e1 e1' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e1 e1') ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons1 e1 Γ :: F1) (FCons1 e1' Γ' :: F2)).
Proof.
  intros n e1 e1' Γ Γ' HGc1 HGc2 He m F1 F2 Hmn HF.
  specialize (He m Hmn).
  apply Frel_closed in HF as HFc. destruct HFc as [HFc1 HFc2].
  destruct He as [He1c [He1'c He]].
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v2 Γ1 Γ2 HV D.
  inv D. eapply He in H5 as [i D].
  exists (S i). constructor. exact D. lia.
  apply Vrel_closed in HV as HVc. destruct HVc as [HVc1 HVc2].
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0k v0 v3 Γ0 Γ3 HV' D.
  inv D. eapply HF in H6 as [i D].
  exists (S i). constructor. exact D. lia.
  eapply Vrel_VCons_compat_closed.
  all: eapply Vrel_downclosed; eauto.
  Unshelve. lia. lia.
Qed.

Lemma Frel_FCons2 :
  forall n v2 v2' Γ Γ', 
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (* ^^^ we've discussed that we don't even need envs in FCons2, but they are checked for
         closedness anyway.
  *)
  (forall m, m <= n -> Vrel m v2 v2') ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons2 v2 Γ :: F1) (FCons2 v2' Γ' :: F2)).
Proof.
  intros n v2 v2' Γ Γ' HGc1 HGc2 HV m F1 F2 Hmn HF.
  specialize (HV m Hmn).
  apply Vrel_closed in HV as HVc. destruct HVc as [HVc1 HVc2].
  apply Frel_closed in HF as HFc. destruct HFc as [HFc1 HFc2].
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v0 Γ1 Γ2 HV' D.
  inv D. eapply HF in H5 as [i D].
  exists (S i). constructor. exact D. lia.
  eapply Vrel_VCons_compat_closed.
  all: eapply Vrel_downclosed; eauto.
  Unshelve. lia. lia.
Qed.

Lemma Frel_FCase :
  forall n p e2 e2' e3 e3' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (forall m, m <= n -> forall vl1 vl2, length vl1 = pat_vars p -> list_biforall (Vrel m) vl1 vl2 ->
    exp_rel m (fun m _ => Vrel m) (vl1 ++ Γ) (vl2 ++ Γ') e2 e2') ->
  (forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e3 e3') ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 ->
    Frel m (FCase p e2 e3 Γ :: F1) (FCase p e2' e3' Γ' :: F2)).
Proof.
  intros n p e2 e2' e3 e3' Γ Γ' HGc1 HGc2 He2 He3 m F1 F2 Hmn HF.
  specialize (He3 m Hmn). destruct He3 as [He3s [He3's He3]].
  specialize (He2 m Hmn (repeat VNil (pat_vars p)) (repeat VNil (pat_vars p))) as He2'.
  rewrite repeat_length in He2'.
  assert (list_biforall (Vrel m) (repeat VNil (pat_vars p)) (repeat VNil (pat_vars p))) as Hbfa.
  { clear. remember (pat_vars p) as k. clear Heqk.
    induction k; simpl; constructor.
    apply Vrel_VNil_compat_closed. exact IHk. }
  specialize (He2' eq_refl Hbfa). clear Hbfa.
  destruct He2' as [He2s [He2's _]].
  rewrite length_app, repeat_length in He2s, He2's.
  apply Frel_closed in HF as HFc. destruct HFc as [HFc1 HFc2]. 
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v2 Γ1 Γ2 HV D.
  inv D.
  * eapply match_pattern_Vrel in HV as HP. 2: exact H7.
    destruct HP as [l2 [HPv2 HPbfa]].
    apply match_pattern_length in H7 as HPl.
    eapply He2 in H8 as [i D].
    exists (S i). eapply term_case_true. exact HPv2. exact D.
    2: auto.
    2: eapply Vrel_biforall_downclosed; eauto. 2: reflexivity. lia.
    eapply Frel_downclosed. eauto.
    Unshelve. lia. lia.
  * eapply nomatch_pattern_Vrel in HV as HP. 2: exact H7.
    eapply He3 in H8 as [i D].
    exists (S i). apply term_case_false. auto. exact D. lia.
    eapply Frel_downclosed. eauto.
    Unshelve. lia.
Qed.

Lemma Frel_FApp1 :
  forall n l l' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  list_biforall (fun e e' => forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e e') l l' ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp1 l Γ :: F1) (FApp1 l' Γ' :: F2)).
Proof.
  intros n l l' Γ Γ' HΓ HΓ' He m F1 F2 Hmn HF.
  destruct HF as [HF1 [HF2 HF]].
  assert (Forall (λ e : Exp, EXP length Γ ⊢ e) l /\ 
          Forall (λ e : Exp, EXP length Γ' ⊢ e) l') as Hs.
  { eapply biforall_impl in He.
    apply exp_rel_biforall_Forall_scope in He. eauto.
    intros. apply H. exact Hmn. }
  destruct Hs as [Hsl Hsl'].
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v2 Γ1 Γ2 HV D.
  destruct (Vrel_closed _ _ _ HV).
  inv D; subst.
  * inv He.
    destruct v1; try discriminate. simpl in H7.
    destruct vl; try discriminate. inv H7.
    rewrite Vrel_Fix_eq in HV. destruct HV as [_ [_ HV]].
    destruct v2; try contradiction.
    destruct HV as [Hl HV]. subst vl.
    eapply step_terminates_one. constructor. reflexivity.
    assert (VClos Γ0 0 res :: Γ0 = VClos Γ0 0 res :: [] ++ Γ0) by reflexivity.
    rewrite H1 in H8. clear H1.
    eapply HV in H8. exact H8.
    5: reflexivity. lia. 1-2: reflexivity. constructor.
    split. 2: split. 1-2: auto.
    intros m0 Hm0k v1 v2 Γ4 Γ5 HV' D. eapply HF in D. exact D. lia. exact HV'.
  * inv He. subst.
    eapply step_terminates_one. constructor.
    eapply H3 in H7. exact H7. exact Hmn. lia.
    apply Erel_EApp_compat_ind; auto.
    + eapply biforall_impl in H5. eapply exp_rel_biforall_downclosed in H5. eauto.
      intros. apply H4. reflexivity.
    + constructor.
    + eapply Vrel_downclosed. eauto.
    + intros m0 Hm0k v0 v3 Γ0 Γ3 HV' D.
      eapply HF in D; eauto. lia.
Unshelve. lia. lia.
Qed.

Lemma Frel_FBIF1 :
  forall n l l' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  list_biforall (fun e e' => forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e e') l l' ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FBIF1 l Γ :: F1) (FBIF1 l' Γ' :: F2)).
Proof.
  intros n l l' Γ Γ' HΓ HΓ' He m F1 F2 Hmn HF.
  destruct HF as [HF1 [HF2 HF]].
  assert (Forall (λ e : Exp, EXP length Γ ⊢ e) l /\ 
          Forall (λ e : Exp, EXP length Γ' ⊢ e) l') as Hs.
  { eapply biforall_impl in He.
    apply exp_rel_biforall_Forall_scope in He. eauto.
    intros. apply H. exact Hmn. }
  destruct Hs as [Hsl Hsl'].
  split. 2: split.
  1-2: constructor; auto; constructor; auto.
  intros m0 Hm0m v1 v2 Γ1 Γ2 HV D.
  destruct (Vrel_closed _ _ _ HV).
  inv D; subst.
  * inv He.
    destruct v1; try discriminate. simpl in H7.
    destruct l; try discriminate.
    destruct s; try discriminate.
    destruct a; try discriminate.
    destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
    destruct s; discriminate.
  * inv He. subst.
    eapply step_terminates_one. constructor.
    eapply H3 in H7. exact H7. exact Hmn. lia.
    apply Erel_EBIF_compat_ind; auto.
    + eapply biforall_impl in H5. eapply exp_rel_biforall_downclosed in H5. eauto.
      intros. apply H4. reflexivity.
    + constructor.
    + eapply Vrel_downclosed. eauto.
    + intros m0 Hm0k v0 v3 Γ0 Γ3 HV' D.
      eapply HF in D; eauto. lia.
Unshelve. lia. lia.
Qed.

Lemma Frel_FApp2 :
  forall n v v' l l' el el' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (forall m, m <= n -> Vrel m v v') ->
  list_biforall (fun v v' => forall m, m <= n -> Vrel m v v') l l' ->
  list_biforall (fun e e' => forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e e') el el' ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp2 v l el Γ :: F1) (FApp2 v' l' el' Γ' :: F2)).
Proof.
  intros. destruct H5, H6.
  eapply Erel_EApp_compat_ind; eauto.
  * eapply biforall_impl in H3. eapply exp_rel_biforall_downclosed in H3. eauto.
    intros. apply H8. reflexivity.
  * eapply biforall_impl in H2. eapply Vrel_biforall_downclosed in H2. eauto.
    intros. apply H8. reflexivity.
Unshelve. lia. lia.
Qed.

Lemma Frel_FBIF2 :
  forall n v v' l l' el el' Γ Γ',
  ENVCLOSED Γ -> ENVCLOSED Γ' ->
  (forall m, m <= n -> Vrel m v v') ->
  list_biforall (fun v v' => forall m, m <= n -> Vrel m v v') l l' ->
  list_biforall (fun e e' => forall m, m <= n -> exp_rel m (fun m _ => Vrel m) Γ Γ' e e') el el' ->
  (forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FBIF2 v l el Γ :: F1) (FBIF2 v' l' el' Γ' :: F2)).
Proof.
  intros. destruct H5, H6.
  eapply Erel_EBIF_compat_ind; eauto.
  * eapply biforall_impl in H3. eapply exp_rel_biforall_downclosed in H3. eauto.
    intros. apply H8. reflexivity.
  * eapply biforall_impl in H2. eapply Vrel_biforall_downclosed in H2. eauto.
    intros. apply H8. reflexivity.
Unshelve. lia. lia.
Qed.

Theorem Frel_Fundamental :
  forall F n,
    FSCLOSED F ->
    Frel n F F.
Proof.
  induction F; intros n HF.
  * split. 2: split. 1-2: auto.
    intros. exists 0. constructor.
  * split. 2: split. 1-2: auto.
    intros m Hmn v1 v2 Γ1 Γ2 HV D.
    destruct a; inversion HF; inversion H1; subst.
    + eapply Frel_FApp1; eauto.
      clear -H5 H6.
      induction l;[constructor|].
      inv H6. apply IHl in H2. constructor;[|auto].
      intros. eapply Erel_Fundamental; eauto.
      apply Grel_Fundamental; auto.
    + eapply Frel_FBIF1; eauto.
      clear -H5 H6.
      induction l;[constructor|].
      inv H6. apply IHl in H2. constructor;[|auto].
      intros. eapply Erel_Fundamental; eauto.
      apply Grel_Fundamental; auto.
    + eapply Frel_FLet; eauto.
      intros. eapply Erel_Fundamental; eauto.
      apply Grel_cons; auto. apply Grel_Fundamental; auto.
    + eapply Frel_FCase; eauto.
      - intros.
        eapply Erel_Fundamental; eauto.
        apply Grel_app; auto.
        ** split; auto.
        ** apply Grel_Fundamental; auto.
      - intros. eapply Erel_Fundamental; eauto.
        apply Grel_Fundamental; auto.
    + eapply Frel_FCons1; eauto.
      intros. eapply Erel_Fundamental; eauto.
      apply Grel_Fundamental; auto.
    + eapply Frel_FCons2; eauto.
      intros. apply Vrel_Fundamental. auto.
    + eapply Frel_FApp2. 10: exact D. all: eauto.
      - intros. apply Vrel_Fundamental; auto.
      - clear -H9.
        induction l; constructor; inv H9; auto.
        intros. apply Vrel_Fundamental. auto.
      - clear - H10 H7.
        induction el; constructor; inv H10; auto.
        intros. eapply Erel_Fundamental; eauto.
        apply Grel_Fundamental; auto.
    + eapply Frel_FBIF2. 10: exact D. all: auto.
      - intros. apply Vrel_Fundamental. auto.
      - clear -H9. induction l; constructor; inv H9; auto.
        intros. apply Vrel_Fundamental. auto.
      - clear -H10 H7. induction el; constructor; inv H10; auto.
        intros. eapply Erel_Fundamental; eauto.
        apply Grel_Fundamental; auto.
Qed.

Lemma Erel_comp_CIU_implies_Erel : forall {Γ e1 e2 e3},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e2 e3 ->
    Erel_open Γ e1 e3.
Proof.
  intros Γ e1 e2 e3 He HCIU.
  split. 2: split.
  1: { apply Erel_open_scope_l in He. apply Grel_length_l in H. rewrite H. auto. }
  1: { apply CIU_open_scope_r in HCIU. apply Grel_length_r in H. rewrite H. auto. }
  intros m Hmn F1 F2 HF D.
  eapply He in D; eauto.
  apply Grel_closed in H as Hc. destruct Hc as [Hc1 Hc2].
  destruct H as [Hl Hg].
  apply biforall_length in Hg as Hl'.
  apply HCIU in D; auto.
  lia. apply HF.
Qed.

Lemma CIU_implies_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    Erel_open Γ e1 e2.
Proof.
  intros.
  eapply Erel_comp_CIU_implies_Erel; eauto.
  apply Erel_Fundamental.
  apply CIU_open_scope_l in H. auto.
Qed.

Lemma Erel_implies_CIU : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e1 e2.
Proof.
  intros Γ e1 e2 He Γ' HΓ' Hc.
  subst Γ.
  destruct (Erel_open_scope _ _ _ He) as [Hes1 Hes2].
  repeat split; auto.
  intros Fs HFs D.
  destruct D as [x D].
  eapply He in D; eauto.
  apply Grel_Fundamental; auto.
  apply Frel_Fundamental; auto.
Qed.

Theorem CIU_Fun_compat :
  forall Γ vl b b',
    CIU_open (S vl + Γ) b b' ->
    CIU_open Γ (EFun vl b) (EFun vl b').
Proof.
  intros.
  apply CIU_implies_Erel in H.
  apply Erel_implies_CIU.
  apply Erel_EFun_compat; auto.
Qed.

Definition match_nomatch_pat_gen (v1 : Val) (v2 : Val) : option (Pat * bool) :=
  match v1 with
  | VLit l =>
    match v2 with
    | VLit _ => None
    | _ => Some (PLit l, true)
    end
  | VPid p =>
    match v2 with
    | VPid _ => None
    | _ => Some (PPid p, true)
    end
  | VNil =>
    match v2 with
    | VNil => None
    | _ => Some (PNil, true)
    end
  | VCons v1_1 v1_2 =>
    match v2 with
    | VCons _ _ => None
    | _ => Some (PCons PVar PVar, true)
    end
  | VClos _ _ _ => 
    match v2 with
    | VLit l => Some (PLit l, false)
    | VPid p => Some (PPid p, false)
    | VNil => Some (PNil, false)
    | VCons v1_1 v1_2 => Some (PCons PVar PVar, false)
    | VClos _ _ _ => None
    end
  end.

Lemma match_nomatch_pat_gen_correct :
  forall v1 v2 p b,
    (* if the pattern generator function returns a pattern... *)
    match_nomatch_pat_gen v1 v2 = Some (p, b) ->
      (* true implies that the direction is forwards, v1 matches but v2 doesn't *)
      (b = true ->
      (exists (lv : list Val), match_pattern p v1 = Some lv) /\
      match_pattern p v2 = None) /\
      
      (* false implies that the direction is backwards, v2 matches but v1 doesn't *)
      (b = false ->
      (exists (lv : list Val), match_pattern p v2 = Some lv) /\
      match_pattern p v1 = None).
Proof.
  intros; destruct v1, v2; try discriminate;
    simpl in H; inv H; simpl; split; intros; try discriminate; split; try reflexivity;
    try rewrite lit_eqb_refl; try rewrite Nat.eqb_refl; eexists; reflexivity.
Qed.

Definition inf := EApp (EFun 0 (EApp (EVar 0) [])) [].

Lemma inf_diverges :
  forall n Fs Γ, ~|Γ, Fs, inf| n↓.
Proof.
  unfold inf.
  intros. intro.
  inv H. inv H5. inv H4. inv H3.
  induction k using lt_wf_ind.
  inv H6. inv H5. inv H1. inv H4. inv H5.
  apply H in H7. destruct H7. lia.
Qed.

Lemma Grel_nil_len :
  forall n Γ,
    Grel n Γ (repeat VNil Γ) (repeat VNil Γ).
Proof.
  intros. split. rewrite repeat_length. reflexivity.
  induction Γ; simpl; constructor; auto. apply Vrel_VNil_compat.
Qed.

Lemma Erel_match_nomatch_false :
  forall v1 v2 p b,
    match_nomatch_pat_gen v1 v2 = Some (p, b) ->
    forall Γ,
    Erel_open Γ v1 v2 /\ Erel_open Γ v2 v1 -> False.
Proof.
  intros. destruct H0. apply match_nomatch_pat_gen_correct in H.
  destruct H.
  unfold Erel_open, exp_rel in H0, H1.
  pose proof (Grel_nil_len 1 Γ) as Hg.
  specialize (H0 _ _ _ Hg) as [_ [_ H0]].
  specialize (H1 _ _ _ Hg) as [_ [_ H1]].
  assert (Frel 1 [FCase p (˝VNil) inf []] [FCase p (˝VNil) inf []]).
  { apply Frel_Fundamental. repeat constructor; intros; inv H3. }
  specialize (H0 1 ltac:(lia) _ _ H3).
  specialize (H1 1 ltac:(lia) _ _ H3). clear H3.
  
  (* this is when we need to check wich direction we're going *)
  destruct b.
  * clear H2 H1.
    specialize (H eq_refl) as [[lv H] H'].
    assert (| repeat VNil Γ, [FCase p (˝ VNil) (° inf) []], ˝ v1 | 1 ↓).
    { eapply term_case_true. exact H. constructor. }
    specialize (H0 H1). clear H1.
    destruct H0 as [k D]. inv D. apply inf_diverges in H9. assumption.
  * clear H H0.
    specialize (H2 eq_refl) as [[lv H] H'].
    assert (| repeat VNil Γ, [FCase p (˝ VNil) (° inf) []], ˝ v2 | 1 ↓).
    { eapply term_case_true. exact H. constructor. }
    specialize (H1 H0). clear H0.
    destruct H1 as [k D]. inv D. apply inf_diverges in H9. assumption.
Qed.

Lemma Erel_Val_compat_backwards :
  forall {Γ v1 v2},
    Erel_open Γ (˝ v1) (˝ v2) /\ Erel_open Γ (˝ v2) (˝ v1) ->
    Vrel_all v1 v2 /\ Vrel_all v2 v1.
Proof.
  intros Γ v1 v2.
  remember v1 as v1'.
  revert Γ v2 v1' Heqv1'.
  induction v1 using Val_ind2 with
  (P  := fun e => (1 = 1))
  (PN := fun n => (2 = 2))
  (Q  := fun le => (3 = 3))
  (R  := fun lv => (4 = 4)); auto; intros;
                             pose proof (Erel_match_nomatch_false v1' v2) as Hmnm;
                             destruct v2; subst v1';
                             try (destruct (Hmnm _ _ eq_refl _ H)); clear Hmnm.
  * destruct (lit_eqb l0 l) eqn:Hleq.
    + apply lit_eqb_eq in Hleq. subst l0.
      split; apply Vrel_Fundamental; constructor.
    + destruct H as [H _]. unfold Erel_open, exp_rel in H.
      pose proof (Grel_nil_len 1 Γ) as Hg.
      specialize (H _ _ _ Hg) as [_ [_ H]]. clear Hg.
      assert (Frel 1 [FCase (PLit l) (˝VNil) inf []] [FCase (PLit l) (˝VNil) inf []]).
      { apply Frel_Fundamental. repeat constructor; intros; inv H0. }
      specialize (H 1 ltac:(lia) _ _ H0). clear H0.
      assert (| repeat VNil Γ, [FCase (PLit l) (˝ VNil) (° inf) []], ˝ VLit l | 1 ↓).
      { eapply term_case_true. simpl. rewrite lit_eqb_refl. reflexivity. constructor. }
      specialize (H H0). clear H0.
      destruct H as [k D]. inv D.
      - simpl in H7. rewrite Hleq in H7. discriminate.
      - apply inf_diverges in H8. contradiction.
  * destruct (p =? n) eqn:Hpn.
    + apply Nat.eqb_eq in Hpn. subst n.
      split; apply Vrel_Fundamental; constructor.
    + destruct H as [H _]. unfold Erel_open, exp_rel in H.
      pose proof (Grel_nil_len 1 Γ) as Hg.
      specialize (H _ _ _ Hg) as [_ [_ H]]. clear Hg.
      assert (Frel 1 [FCase (PPid n) (˝VNil) inf []] [FCase (PPid n) (˝VNil) inf []]).
      { apply Frel_Fundamental. repeat constructor; intros; inv H0. }
      specialize (H 1 ltac:(lia) _ _ H0). clear H0.
      assert (| repeat VNil Γ, [FCase (PPid n) (˝ VNil) (° inf) []], ˝ VPid n | 1 ↓).
      { eapply term_case_true. simpl. rewrite Nat.eqb_refl. reflexivity. constructor. }
      specialize (H H0). clear H0.
      destruct H as [k D]. inv D.
      - simpl in H7. rewrite Hpn in H7. discriminate.
      - apply inf_diverges in H8. contradiction.
  * split; apply Vrel_Fundamental; constructor.
  * specialize (IHv1_1 Γ v2_1 v1_1 eq_refl).
    specialize (IHv1_2 Γ v2_2 v1_2 eq_refl).
    destruct H as [He1 He2].
    destruct (Erel_open_scope _ _ _ He1) as [Hs1 Hs2].
    inv Hs1. inv Hs2. inv H0. inv H1.
    pose proof (Grel_closed _ _ _ _ (Grel_nil_len 1 Γ)) as [HΓ _].
    assert (length (repeat VNil Γ) = Γ) as Hl by (now apply repeat_length).
    split; apply Vrel_VCons_compat; try apply IHv1_1; try apply IHv1_2; split.
    all: apply Erel_implies_CIU in He1, He2.
    all: specialize (He1 _ Hl HΓ).
    all: specialize (He2 _ Hl HΓ).
    all: destruct He1 as [_ [_ [_ He1]]].
    all: destruct He2 as [_ [_ [_ He2]]].
    all: apply CIU_implies_Erel; unfold CIU_open, CIU; intros.
    all: split; auto; split;[constructor; auto|]; split;[constructor; auto|]; intros.
    all: clear -He1 He2 H1 H6.
    2,4,6,8: shelve.
    1: specialize (He1 (FCase (PCons PVar PVar) (EVar 0) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    2: specialize (He1 (FCase (PCons PVar PVar) (EVar 1) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    3: specialize (He1 (FCase (PCons PVar PVar) (EVar 0) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    4: specialize (He1 (FCase (PCons PVar PVar) (EVar 1) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    all: destruct He1 as [i D];
         inv D; inv H9; inv H10; inv H0;
         eapply value_terminates_env_indep; eexists; eauto.
    Unshelve.
    1: specialize (He2 (FCase (PCons PVar PVar) (EVar 0) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    2: specialize (He2 (FCase (PCons PVar PVar) (EVar 1) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    3: specialize (He2 (FCase (PCons PVar PVar) (EVar 0) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    4: specialize (He2 (FCase (PCons PVar PVar) (EVar 1) (˝VNil) [] :: Fs) 
                      ltac:(repeat constructor; auto)
                      ltac:(eapply step_terminates_any with (k :=2);
                            [repeat econstructor|];
                            eapply value_terminates_env_indep; exact H6)).
    all: destruct He2 as [i D];
         inv D; inv H9; inv H10; inv H0;
         eapply value_terminates_env_indep; eexists; eauto.
  * destruct H.
    destruct (Erel_open_scope _ _ _ H) as [Hc1 Hc2].
    inv Hc1. inv Hc2.
    split.
    + intro. rewrite Vrel_Fix_eq. simpl. split. 2: split. 1-2: auto.
      destruct (vl =? vl0) eqn:Hl.
      2: admit.
      rewrite Nat.eqb_eq in Hl. subst vl0.
      intros. unfold exp_rel. 
      clear H0.
      apply Erel_implies_CIU in H. unfold CIU_open, CIU in H.
    +
Admitted.












Lemma term_eval_open_helper_app :
  forall hds' hds e' k vals v Γ Γapp Fs v1,
  (∀ m : nat,
    m < S k
    → ∀ (Γ : list Val) (Fs : FrameStack) (e : Exp),
        | Γ, Fs, e | m ↓
           → ∃ (v : Val) (k : nat) (Γ' : Env),
             ⟨ Γ, [], e ⟩ -[ k ]-> ⟨ Γ', [], ˝ v ⟩
               ∧ k ≤ m) ->
  | Γ, FApp2 v vals (hds' ++ e' :: hds) Γapp :: Fs, ˝v1 | k ↓ ->
  exists k0 hds'',
  ⟨ Γ, [FApp2 v vals (hds' ++ e' :: hds) Γapp], ˝v1 ⟩ -[k0]-> 
  ⟨ Γapp, [FApp2 v (vals ++ v1 :: hds'') hds Γapp] , e'⟩ /\ k0 <= k.
Proof.
  induction hds'; intros; simpl.
  * inv H0. do 2 eexists. repeat split.
    1: {
      econstructor. constructor. constructor.
    }
    lia.
  * inv H0.
    eapply H in H10 as D'; auto.
    destruct D' as [v' [k' [Γ' [HD' Hlt']]]].
    eapply terminates_step_any_2 in H10. 2: {
      eapply frame_indep_core in HD'. exact HD'.
    }
    simpl in H10.
    apply (IHhds' hds e' (k0 - k') (vals ++ [v1])
                v Γ' Γapp Fs v') in H10 as D''; try by auto.
    2: {
      intros. eapply H; try eassumption. lia.
    }
    destruct D'' as [v'' [k'' [HD'' Hlt'']]].
    eapply terminates_step_any_2 in H10. 2: {
      eapply frame_indep_core in HD''. exact HD''.
    }
    do 2 eexists. repeat split.
    1: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD'. exact HD'.
      simpl. rewrite <- app_assoc in HD''. simpl in HD''.
      exact HD''.
    }
    lia.
Qed.

Lemma term_eval_open_helper_bif :
  forall hds' hds e' k vals v Γ Γapp Fs v1,
  (∀ m : nat,
    m < S k
    → ∀ (Γ : list Val) (Fs : FrameStack) (e : Exp),
      | Γ, Fs, e | m ↓
        → ∃ (v : Val) (k : nat) (Γ' : Env),
          ⟨ Γ, [], e ⟩ -[ k ]-> ⟨ Γ', [], ˝ v ⟩
            ∧ k ≤ m) ->
  | Γ, FBIF2 v vals (hds' ++ e' :: hds) Γapp :: Fs, ˝v1 | k ↓ ->
  exists k0 hds'',
  ⟨ Γ, [FBIF2 v vals (hds' ++ e' :: hds) Γapp], ˝v1 ⟩ -[k0]-> 
  ⟨ Γapp, [FBIF2 v (vals ++ v1 :: hds'') hds Γapp] , e'⟩ /\ k0 <= k.
Proof.
  induction hds'; intros; simpl.
  * inv H0. do 2 eexists. repeat split.
    1: {
      econstructor. constructor. constructor.
    }
    lia.
  * inv H0.
    eapply H in H10 as D'; auto.
    destruct D' as [v' [k' [Γ' [HD' Hlt']]]].
    eapply terminates_step_any_2 in H10. 2: {
      eapply frame_indep_core in HD'. exact HD'.
    }
    simpl in H10.
    apply (IHhds' hds e' (k0 - k') (vals ++ [v1])
                v Γ' Γapp Fs v') in H10 as D''; try by auto.
    2: {
      intros. eapply H; try eassumption. lia.
    }
    destruct D'' as [v'' [k'' [HD'' Hlt'']]].
    eapply terminates_step_any_2 in H10. 2: {
      eapply frame_indep_core in HD''. exact HD''.
    }
    do 2 eexists. repeat split.
    1: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD'. exact HD'.
      simpl. rewrite <- app_assoc in HD''. simpl in HD''.
      exact HD''.
    }
    lia.
Qed.



Theorem term_eval_empty_open :
  forall x Γ Fs e,
    | Γ, Fs, e | x ↓ ->
    exists v k Γ',
      ⟨ Γ, [], e ⟩ -[k]-> ⟨ Γ', [], ˝v ⟩ /\ k <= x.
Proof.
  induction x using lt_wf_ind; intros * D; inv D.
  all: try by exists v, 0, Γ; repeat split; auto; try constructor; try lia.
  * exists v0, 0, Γ. repeat split; constructor; lia.
  * exists v0, 0, Γ. repeat split; constructor; lia.
  * exists v0, 0, Γ. repeat split; constructor; lia.
  * exists v0, 0, Γ. repeat split; constructor; lia.
  * exists val, 0, Γ. repeat split; constructor; lia.
  * exists v2, 0, Γ. repeat split; constructor; lia.
  * exists v1, 0, Γ. repeat split; constructor; lia.
  * eapply H in H0 as D'; auto.
    destruct D' as [v1 [k1 [Γ1 [HD1 Hlt1]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    eapply H in H3 as D''; auto. 2: lia.
    destruct D'' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
    do 3 eexists. repeat split.
    1: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
      econstructor. constructor.
      eapply frame_indep_core in HD2. exact HD2.
    }
    lia.
  * eapply H in H0 as D'; auto.
    destruct D' as [v1 [k1 [Γ1 [HD1 Hlt1]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H8 as D'; auto. 2: {
        lia.
      }
      destruct D' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      eapply terminates_step_any_2 in H8. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      do 3 eexists. repeat split.
      1: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. constructor. eassumption.
        eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
        constructor.
      }
      lia.
    }
    { (* inductive case *)
      eapply H in H3 as D'. 2: {
        lia.
      }
      destruct D' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      eapply terminates_step_any_2 in H3. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      simpl in H3. destruct (length l) eqn:L.
      * (* single parameter: *)
        apply length_zero_iff_nil in L. subst.
        inv H3.
        eapply H in H10 as X; try eassumption. 2: lia.
        destruct X as [v5 [k5' [Γ5 [HD5 Hlt5]]]].
        do 3 eexists. repeat split.
        1: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        lia.

        (* more parameters: *)
      * apply eq_sym, last_element_exists in L as [l' [x ?]].
        subst.
        eapply (term_eval_open_helper_app l' []) in H3 as X; try eassumption.
        all: try by constructor.
        2: {
          intros. eapply H. lia. all: eassumption.
        }
        destruct X as [k3 [v3 [HD3 Hlt3]]].
        eapply terminates_step_any_2 in H3. 2: eapply frame_indep_core in HD3; exact HD3.
        eapply H in H3 as X; try eassumption. 2: { lia. }
        destruct X as [v4 [k4 [Γ4 [HD4 Hlt4]]]].
        simpl in H3.
        eapply terminates_step_any_2 in H3. 2: eapply frame_indep_core in HD4; exact HD4.
        simpl in H3. inv H3.
        
        eapply H in H10 as X; try eassumption. 2: lia.
        destruct X as [v5 [k5' [Γ5 [HD5 Hlt5]]]].
        
        do 3 eexists. repeat split.
        1: {
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
        lia.
    }
  * eapply H in H0 as D'; auto.
    destruct D' as [v1 [k1 [Γ1 [HD1 Hlt1]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H8 as D'; auto. 2: {
        lia.
      }
      destruct D' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      eapply terminates_step_any_2 in H8. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      do 3 eexists. repeat split.
      1: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. constructor. eassumption.
        eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
        constructor.
      }
      lia.
    }
    { (* inductive case *)
      eapply H in H3 as D'. 2: {
        lia.
      }
      destruct D' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      eapply terminates_step_any_2 in H3. 2: {
        eapply frame_indep_core in HD2. exact HD2.
      }
      simpl in H3. destruct (length l) eqn:L.
      * (* single parameter: *)
        apply length_zero_iff_nil in L. subst.
        inv H3.
        eapply H in H10 as X; try eassumption. 2: lia.
        destruct X as [v5 [k5' [Γ5 [HD5 Hlt5]]]].
        do 3 eexists. repeat split.
        1: {
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
          econstructor. constructor.
          eapply transitive_eval. eapply frame_indep_core in HD2. exact HD2.
          simpl. econstructor. constructor. cbn. eassumption.
          exact HD5.
        }
        lia.

        (* more parameters: *)
      * apply eq_sym, last_element_exists in L as [l' [x ?]].
        subst.
        eapply (term_eval_open_helper_bif l' []) in H3 as X; try eassumption.
        all: try by constructor.
        2: {
          intros. eapply H. lia. all: eassumption.
        }
        destruct X as [k3 [v3 [HD3 Hlt3]]].
        eapply terminates_step_any_2 in H3. 2: eapply frame_indep_core in HD3; exact HD3.
        eapply H in H3 as X; try eassumption. 2: { lia. }
        destruct X as [v4 [k4 [Γ4 [HD4 Hlt4]]]].
        simpl in H3.
        eapply terminates_step_any_2 in H3. 2: eapply frame_indep_core in HD4; exact HD4.
        simpl in H3. inv H3.
        
        eapply H in H10 as X; try eassumption. 2: lia.

        destruct X as [v5 [k5' [Γ5 [HD5 Hlt5]]]].
        
        do 3 eexists. repeat split.
        1: {
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
        lia.
    }
  * eapply H in H0 as D'; auto.
    destruct D' as [v1 [k1 [Γ1 [HD1 Hlt1]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    {
      eapply H in H10 as D''; auto. 2: lia.
      destruct D'' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      do 3 eexists. repeat split.
      1: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. apply red_case_true.
        eapply frame_indep_core in HD2.
        eassumption. exact HD2.
      }
      lia.
    }
    {
      eapply H in H10 as D''; auto. 2: lia.
      destruct D'' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
      do 3 eexists. repeat split.
      1: {
        econstructor. constructor.
        eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
        econstructor. apply red_case_false. assumption.
        eapply frame_indep_core in HD2.
        exact HD2.
      }
      lia.
    }
  * eapply H in H0 as D'; auto.
    destruct D' as [v1 [k1 [Γ1 [HD1 Hlt1]]]].
    eapply terminates_step_any_2 in H0. 2: {
      eapply frame_indep_core in HD1. exact HD1.
    }
    inv H0.
    eapply H in H3 as D''; auto. 2: lia.
    destruct D'' as [v2 [k2 [Γ2 [HD2 Hlt2]]]].
    do 3 eexists. repeat split.
    1: {
      econstructor. constructor.
      eapply transitive_eval. eapply frame_indep_core in HD1. exact HD1.
      econstructor. constructor.
      eapply transitive_eval.
      eapply frame_indep_core in HD2. exact HD2.
      econstructor. constructor.
      constructor.
    }
    eapply terminates_step_any_2 in H3. 2: eapply frame_indep_core in HD2; exact HD2. inv H3.
    lia.
  * do 3 eexists. repeat split.
    1: {
      econstructor. constructor. constructor.
    }
    lia.
  * do 3 eexists. repeat split.
    1: {
      econstructor. constructor. eassumption. constructor.
    }
    lia.
Unshelve.
  exact [].
Qed.

Lemma env_ext_clos_helper :
forall (k : nat) (Γ Γ': Env) (Fs : FrameStack) (vl : nat) (e0 : Exp),
  (∀ m : nat,
    m < S k
    → ∀ (Γ : Env) (Fs : FrameStack) (e : Exp),
        | Γ, Fs, e | m ↓ → ∀ Γ' : list Val, | Γ ++ Γ', Fs, e | ↓) ->
    | Γ, Fs, ˝ VClos Γ vl e0 | k ↓ ->
  | Γ ++ Γ', Fs, ˝ VClos (Γ ++ Γ') vl e0 | ↓.
Proof.
  intros.
  apply value_terminates_env_indep with (Γ1 := []).
  apply value_terminates_in_k_env_indep with (Γ2 := []) in H0.
  
  inv H0.
  * exists 0. constructor.
  * exists (S k0). constructor. admit.
  * admit.
  * admit.
  * simpl in H2. destruct vl; try discriminate. inv H2.
    exists (S k0). econstructor. reflexivity. simpl.
Admitted.

(*
1 goal
k : nat
H :
  ∀ m : nat,
    m < S k
    → ∀ (Γ : Env) (Fs : FrameStack) (e : Exp),
        | Γ, Fs, e | m ↓ → ∀ Γ' : list Val, | Γ ++ Γ', Fs, e | ↓
Γ : Env
Fs : FrameStack
Γ' : list Val
vl : nat
e0 : Exp
H0 : | Γ, Fs, ˝ VClos Γ vl e0 | k ↓
______________________________________(1/1)
| Γ ++ Γ', Fs, ° EFun vl e0 | ↓

*)


Lemma env_ext :
  forall Γ Fs e,
    | Γ, Fs, e | ↓ ->
    forall Γ',
      | Γ ++ Γ', Fs, e | ↓.
Proof.
  intros. destruct H. exists x.
  revert Γ Fs e H Γ'.
  induction x using lt_wf_ind; intros Γ Fs e D Γ'; inv D.
  1: constructor.
  1-13: econstructor; eassumption.
  * constructor. apply H. lia.
    eapply term_eval_empty_open in H0 as Ho.
    destruct Ho as [v [k0 [Γ'' [Ho Hk]]]].
    eapply terminates_step_any_2 in H0.
    2: eapply frame_indep_core in Ho; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho; eauto.
    2: lia.
    simpl in *.
    inv H0. constructor.
    rewrite app_comm_cons.
    apply H. lia. auto.
  * constructor. apply H. lia.
    eapply term_eval_empty_open in H0 as Ho.
    destruct Ho as [v [k0 [Γ'' [Ho Hk]]]].
    eapply terminates_step_any_2 in H0.
    2: eapply frame_indep_core in Ho; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho; eauto.
    2: lia.
    simpl in *.
    inv H0.
    + (* 0 arguments *)
      econstructor. eassumption. eassumption.
    + econstructor. apply H. lia.
      clear e0 Γ'' Ho.
      eapply term_eval_empty_open in H3 as Ho.
      destruct Ho as [v' [k' [Γ'' [Ho Hk']]]].
      eapply terminates_step_any_2 in H3.
      2: eapply frame_indep_core in Ho; eauto.
      eapply step_term_term.
      1: eapply frame_indep_core in Ho; eauto. 2: lia.
      simpl in *.
      
      remember (k1 - k') as k''.
      remember (@nil Val) as lv.
      clear Heqlv Ho.
      assert (k'' <= k1 - k') as Heq by lia. clear Heqk''.
      generalize dependent lv.
      generalize dependent k''.
      generalize dependent v'.
      generalize dependent Γ''.
      generalize dependent Γ'.
      induction l; intros.
      - (* 1 argument *)
        inv H3. econstructor. eauto. eauto. 
      - (* >1 argument *)
        inv H3. constructor.
        apply H. lia.
        eapply term_eval_empty_open in H11 as Ho.
        destruct Ho as [v'' [k'' [Γ''' [Ho Hk'']]]].
        eapply terminates_step_any_2 in H11.
        2: eapply frame_indep_core in Ho; eauto.
        eapply step_term_term.
        1: eapply frame_indep_core in Ho; eauto. 2: lia. simpl in *.
        eapply IHl. lia. auto.
  * constructor. apply H. lia.
    eapply term_eval_empty_open in H0 as Ho.
    destruct Ho as [v [k0 [Γ'' [Ho Hk]]]].
    eapply terminates_step_any_2 in H0.
    2: eapply frame_indep_core in Ho; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho; eauto.
    2: lia.
    simpl in *.
    inv H0.
    + (* 0 arguments *)
      econstructor. eassumption.
      apply H. lia. auto.
    + econstructor. apply H. lia.
      clear Γ'' Ho.
      eapply term_eval_empty_open in H3 as Ho.
      destruct Ho as [v' [k' [Γ'' [Ho Hk']]]].
      eapply terminates_step_any_2 in H3.
      2: eapply frame_indep_core in Ho; eauto.
      eapply step_term_term.
      1: eapply frame_indep_core in Ho; eauto. 2: lia.
      simpl in *.
      
      remember (k1 - k') as k''.
      remember (@nil Val) as lv.
      clear Heqlv Ho.
      assert (k'' <= k1 - k') as Heq by lia. clear Heqk''.
      generalize dependent lv.
      generalize dependent k''.
      generalize dependent v'.
      generalize dependent Γ''.
      generalize dependent Γ'.
      induction l; intros.
      - (* 1 argument *)
        inv H3. econstructor. eauto.
        apply H. lia. auto.
      - (* >1 argument *)
        inv H3. constructor.
        apply H. lia.
        eapply term_eval_empty_open in H11 as Ho.
        destruct Ho as [v'' [k'' [Γ''' [Ho Hk'']]]].
        eapply terminates_step_any_2 in H11.
        2: eapply frame_indep_core in Ho; eauto.
        eapply step_term_term.
        1: eapply frame_indep_core in Ho; eauto. 2: lia. simpl in *.
        eapply IHl. lia. auto.
  * constructor. apply H. lia.
    eapply term_eval_empty_open in H0 as Ho.
    destruct Ho as [v [k0 [Γ'' [Ho Hk]]]].
    eapply terminates_step_any_2 in H0.
    2: eapply frame_indep_core in Ho; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho; eauto.
    2: lia.
    simpl in *.
    inv H0.
    + eapply term_case_true. eauto.
      rewrite app_assoc.
      apply H. lia. assumption.
    + eapply term_case_false. eauto.
      apply H. lia. assumption.
  * constructor. apply H. lia.
    eapply term_eval_empty_open in H0 as Ho.
    destruct Ho as [v [k0 [Γ'' [Ho Hk]]]].
    eapply terminates_step_any_2 in H0.
    2: eapply frame_indep_core in Ho; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho; eauto.
    2: lia.
    simpl in *.
    inv H0. constructor.
    apply H. lia.
    eapply term_eval_empty_open in H3 as Ho'.
    destruct Ho' as [v1 [k'1 [Γ1 [Ho1 Hk1]]]].
    eapply terminates_step_any_2 in H3.
    2: eapply frame_indep_core in Ho1; eauto.
    eapply step_term_term.
    1: eapply frame_indep_core in Ho1; eauto.
    2: lia.
    simpl in *.
    inv H3. constructor. apply H. lia. auto.
  * constructor.
(*     | VClos Γ vl e0 :: Γ2, Fs, e | k ↓
       ________________________________________________
       | VClos (Γ ++ Γ') vl e0 :: Γ2, Fs, e | k ↓
   *)
  
  apply H. lia.
    admit.
  * econstructor. apply lookup_app_l_Some. eauto.
    apply H. lia. auto.
Admitted.


Lemma term_scope_nottrue :
  ~ (forall Γ Fs (e : NonVal),
    | Γ, Fs, ° e | ↓ -> EXP (length Γ) ⊢ ° e).
Proof.
  intros H.
  specialize (H [] [] (ECase (VLit 0%Z) (PLit (Int 0%Z)) (VNil) (EVar 1))).
  assert (| [], [], ° ECase (˝ VLit 0%Z) (PLit 0%Z) (˝ VNil) (° EVar 1) | ↓).
  { eexists. constructor. eapply term_case_true. reflexivity. simpl. constructor. }
  specialize (H H0). clear H0.
  inv H. inv H1. clear -H7. inv H7. inv H0. lia.
Qed.





Check Erel_Val_compat.








Lemma Erel_Val_compat_backwards :
  forall {Γ v v'},
    Erel_open Γ (˝ v) (˝ v') ->
    Vrel_all v v'.
Proof.
  intros Γ v. revert Γ.
  induction v using Val_ind2 with
  (P  := fun e => (1 = 1))
  (PN := fun n => (2 = 2))
  (Q  := fun le => (3 = 3))
  (R  := fun lv => (4 = 4)); auto; intros. (* don't know these yet *)
  * destruct v'.
    + unfold Erel_open, exp_rel in H.
      intros n. rewrite Vrel_Fix_eq. simpl. admit.
      (* can this be done? *)
    + unfold Erel_open, exp_rel in H.
      specialize (H 1 (repeat VNil Γ) (repeat VNil Γ)).
      assert (Grel 1 Γ (repeat VNil Γ) (repeat VNil Γ)).
      { apply Grel_Fundamental.
        * clear. induction Γ; simpl. constructor. constructor; auto.
        * rewrite repeat_length. reflexivity.
      }
      specialize (H H0). clear H0.
      rewrite repeat_length in H. destruct H as [H1 [H2 H3]].
      specialize (H3 1 (Nat.le_refl _)).
      specialize (H3 (FCase (PLit l) (˝ VNil) (˝ VLit 1%Z) [] :: [])
                     (FCase (PLit l) (˝ VNil) (˝ VLit 1%Z) [] :: [])).
                     (*                            ^ not this, but put a non-terminating
                                                     program here *)
      assert (frame_rel 1 (λ (m' : nat) (_ : m' ≤ 1), Vrel m')
      [FCase (PLit l) (˝ VNil) (˝ VLit 1%Z) []] [FCase (PLit l) (˝ VNil) (˝ VLit 1%Z) []]) by admit.
      (* ^ this would come from Frel_Fundamental *)
      specialize (H3 H). clear H.
      assert (| repeat VNil Γ, [FCase (PLit l) (˝ VNil) (˝ VLit 1%Z) []], ˝ VLit l | 1 ↓).
      { eapply term_case_true. simpl. rewrite lit_eqb_refl. reflexivity.
        simpl. constructor.
      }
      specialize (H3 H). clear H.
      inv H3. inv H. (* again, don't have VLit 1%Z, but something non-terminating *) admit.
      (* the same trick could be done for the others as well which don't match up... *)
    + admit.
    + admit.
    + admit.
  * admit.
  * admit.
  * admit.
  * admit. (* probably the most interesting/difficult one is the case with 2 closures *)
Admitted.








Lemma step_one :
  forall Γ Γ' Fs Fs' e e' v,
    ⟨ Γ, Fs, e ⟩ --> ⟨ Γ', Fs', e' ⟩ ->
    ⟨ Γ', Fs', e' ⟩ -->* v ->
    ⟨ Γ, Fs, e ⟩ -->* v.
Proof.
  intros * D T.
  destruct T as [i [Γ'' T]].
  exists (1 + i). exists Γ''.
  eapply transitive_eval; eauto.
  eapply step_trans; eauto.
  apply step_refl.
Qed.

Definition fold_env (Γ : Env) (e : Exp) : Exp :=
  foldl (fun ex v => ELet (VVal v) ex) e Γ.

Compute fold_env [VLit 1%Z; VLit 2%Z; VLit 3%Z] VNil.

Lemma put_env_back_helper :
  forall v1 Γ Fs e v,
    ⟨ v1 :: Γ, Fs, e ⟩ -->* v ->
    ⟨ Γ, Fs, ° ELet (VVal v1) e ⟩ -->* v.
Proof.
  intros * D.
  eapply step_one. constructor.
  eapply step_one. constructor.
  auto.
Qed.

Lemma put_env_back_app :
  forall Γ Fs e v,
    ⟨ Γ, Fs, e ⟩ -->* v ->
    forall Γ' Γ'',
      Γ = Γ' ++ Γ'' ->
      ⟨ Γ'', Fs, fold_env Γ' e ⟩ -->* v.
Proof.
  induction Γ; intros.
  * destruct Γ'; try discriminate. simpl in H0. inv H0. simpl. assumption.
  * destruct Γ'.
    + simpl in *. subst. assumption.
    + simpl in *. inv H0.
      apply put_env_back_helper in H.
      eapply IHΓ in H. 2: reflexivity. assumption.
Qed.

Lemma put_env_back :
  forall Γ Fs e v,
    ⟨ Γ, Fs, e ⟩ -->* v -> ⟨ [], Fs, fold_env Γ e ⟩ -->* v.
Proof.
  intros * D. eapply put_env_back_app.
  2: rewrite app_nil_r; reflexivity.
  assumption.
Qed.

Corollary put_env_back_term_app :
  forall Γ Fs e,
    | Γ, Fs, e | ↓ ->
    forall Γ' Γ'',
      Γ = Γ' ++ Γ'' ->
      | Γ'', Fs, fold_env Γ' e | ↓.
Proof.
  intros.
  apply terminates_semantics in H. destruct H.
  apply semantics_terminates with (v := x).
  eapply put_env_back_app; eauto.
Qed.

Corollary put_env_back_term :
  forall Γ Fs e,
    | Γ, Fs, e | ↓ -> | [], Fs, fold_env Γ e | ↓.
Proof.
  intros.
  apply terminates_semantics in H. destruct H.
  apply semantics_terminates with (v := x).
  apply put_env_back. auto.
Qed.

Definition plug_f_env (F : Frame) (e : Exp) : Exp :=
  match F with
  | FLet e2 _ => ° ELet e e2
  | FCons1 e1 _ => ° ECons e1 e
  | FCons2 v2 _ => ° ECons e (VVal v2)
  | FCase p e2 e3 _ => ° ECase e p e2 e3
  | FApp1 l _ => ° EApp e l
  | FBIF1 l _ => ° EBIF e l
  | FApp2 v l el _ => ° EApp (VVal v) (map VVal l ++ [e] ++ el)
  | FBIF2 v l el _ => ° EBIF (VVal v) (map VVal l ++ [e] ++ el)
  end.

Definition get_frame_env (F : Frame) : Env :=
  match F with
  | FLet _ Γ => Γ
  | FCons1 _ Γ => Γ
  | FCons2 _ Γ => Γ
  | FCase _ _ _ Γ => Γ
  | FApp1 _ Γ => Γ
  | FBIF1 _ Γ => Γ
  | FApp2 _ _ _ Γ => Γ
  | FBIF2 _ _ _ Γ => Γ
  end.

(* It's not true that expressions need to be scopen in the env to terminate.
   And this is not just true for values, non-closed expressions can terminate as well.
*)
Lemma term_scope_nottrue' :
  ~ (forall Γ Fs (e : NonVal),
    | Γ, Fs, ° e | ↓ -> EXP (length Γ) ⊢ ° e).
Proof.
  intros H.
  specialize (H [] [] (ECase (VLit 0%Z) (PLit (Int 0%Z)) (VNil) (EVar 1))).
  assert (| [], [], ° ECase (˝ VLit 0%Z) (PLit 0%Z) (˝ VNil) (° EVar 1) | ↓).
  { eexists. constructor. eapply term_case_true. reflexivity. simpl. constructor. }
  specialize (H H0). clear H0.
  inv H. inv H1. clear -H7. inv H7. inv H0. lia. 
Qed.

Corollary term_eval_empty_term :
  forall x Γ Fs e,
    AEXP length Γ ⊢ e ->
    ENVCLOSED Γ ->
    | Γ, Fs, e | x ↓ ->
    exists v,
      | Γ, Fs, ˝ v | ↓.
Proof.
  intros * He Hg D.
  apply term_eval_empty in D as D'; auto.
  destruct D' as [v [k [Γ' [_ [D' _]]]]].
  eapply frame_indep_core in D'. simpl in D'.
  apply ex_intro with (x := x) in D.
  eapply terminates_step_any in D;[|eauto].
  apply value_terminates_env_indep with (Γ2 := Γ) in D.
  exists v. auto.
Qed.

Check terminates_in_k_ind.

Lemma terminates_ind_helper :
  forall Γ Fs e k,
    | Γ, Fs, e | S k ↓ ->
    exists Γ' Fs' e',
      ⟨ Γ, Fs, e ⟩ --> ⟨ Γ', Fs', e' ⟩ /\ | Γ', Fs', e' | k ↓.
Proof.
  intros * D. inv D.
  all: try (repeat eexists; eauto; econstructor; auto).
Qed.

Lemma terminates_ind :
  forall (P : Env -> FrameStack -> Exp -> Prop),
    (forall v Γ, P Γ [] (˝ v)) ->
    (forall Γ Fs e Γ' Fs' e',
      ⟨ Γ, Fs, e ⟩ --> ⟨ Γ', Fs', e' ⟩ ->
      | Γ', Fs', e' | ↓ -> P Γ' Fs' e' -> P Γ Fs e) ->
      (forall Γ Fs e,
        | Γ, Fs, e | ↓ -> P Γ Fs e).
Proof.
  intros.
  destruct H1. revert P H H0 Γ Fs e H1. induction x; intros.
  * inv H1. apply H.
  * apply terminates_ind_helper in H1 as [Γ' [Fs' [e' [H1 D]]]].
    apply ex_intro with (x := x) in D as D'.
    specialize (H0 _ _ _ _ _ _ H1 D') as H0'.
    apply H0'. apply IHx; auto.
Qed.

Lemma env_ext :
  forall Γ Fs e,
    AEXP (length Γ) ⊢ e ->
    FSCLOSED Fs ->
    ENVCLOSED Γ ->
    | Γ, Fs, e | ↓ ->
    forall Γ',
      | Γ ++ Γ', Fs, e | ↓.
Proof.
  intros Γ Fs e He HFs Hg D. revert He HFs Hg.
  induction D using terminates_ind; intros.
  * exists 0. constructor.
  * apply scope_preservation in H as H'; auto.
    destruct H' as [He' [HFs' Hg']].
    specialize (IHD He' HFs' Hg' Γ'0).
    admit.
Admitted.

Lemma env_ext' :
  forall Γ Fs e,
(*     AEXP (length Γ) ⊢ e ->
    FSCLOSED Fs ->
    ENVCLOSED Γ -> *)
    | Γ, Fs, e | ↓ ->
    forall Γ',
      | Γ ++ Γ', Fs, e | ↓.
Proof.
  intros Γ Fs e(*  He HFs Hg *) D.
  inv D. exists x. revert Fs e Γ H Γ'.
  
  induction x using lt_wf_ind; intros.
  inv H0.
  15: {
  constructor. apply H. lia.
  
  eapply term_eval_empty in H1 as H1'.
  2-3: admit.
  destruct H1' as [v [k' [Γ'' [HV [H' Hk]]]]].
  eapply terminates_step_any_2 in H1.
  2: { eapply frame_indep_core in H'. exact H'. }
  inv H1.
  eapply step_term_term.
  1: { eapply frame_indep_core in H'. exact H'. }
  2: { lia. }
  simpl. rewrite <- H7. constructor.
  eapply H in H3. 2: lia. 
  simpl in H3. exact H3.
Admitted.
  
(*   intros Γ Fs e He Hg D.
  destruct D as [i D].
  induction D; intros Γ''.
  12: eapply step_terminates_one;[apply red_case_false; try eassumption|];
      try (exists k; eauto).
  2-13: eapply step_terminates_one;[constructor; try eassumption|];
        try (exists k; eauto).
  * exists 0. constructor.
  * eapply step_terminates_one. constructor.
    admit.
  * admit.
Restart.
  intros Γ Fs e He Hg D.
  destruct D as [i D]. revert Γ Fs e He Hg D.
  induction i; intros.
  * inv D. exists 0. constructor.
  * inv D.
    14: { eapply step_terminates_one. constructor.
      inv He.
      apply IHi; auto. apply exp_to_any. auto.
      apply term_eval_empty_term in H3; auto. 2: by apply exp_to_any.
      destruct H3. destruct H.
      
Admitted. *)

Lemma put_back_term :
  forall F e Fs Γ0,
    | Γ0, F :: Fs, e | ↓ -> | get_frame_env F, Fs, plug_f_env F (fold_env Γ0 e) | ↓.
Proof.
  intros F e Fs Γ0 D.
  destruct F; simpl.
  * eapply step_terminates_one. constructor.
    apply put_env_back_term_app with (Γ := Γ0 ++ Γ);[|reflexivity].
    admit.
  *
Admitted.

(* Lemma put_back_term' :
  forall F e Fs Γ0,
    | Γ0, F :: Fs, e | ↓ -> | snd (plug_f_env F (fold_env Γ0 e)), Fs, fst (plug_f_env F (fold_env Γ0 e)) | ↓.
Proof.
  intros F e Fs Γ0 D.
  destruct F.
  * simpl. eapply step_terminates_one. constructor. apply put_env_back_term.
  *
Admitted. *)













