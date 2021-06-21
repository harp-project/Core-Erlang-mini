Require Export SubstSemantics.

Import ListNotations.

(** Because of this, preorder is enough *)
Goal forall T : Type, forall R : relation T, Reflexive R -> Transitive R ->
  let R' := fun x y => R x y /\ R y x in Reflexive R' /\ Symmetric R' /\ Transitive R'.
Proof.
  intros. split. 2: split.
  * intro. unfold R'. split; apply H.
  * intro. intros. unfold R' in *. destruct H1.
    split; auto.
  * intro. intros. unfold R' in *. destruct H1, H2. split.
    - eapply H0; eauto.
    - eapply H0; eauto.
Qed.

Definition frame_rel (n : nat)
                     (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                     (F1 F2 : FrameStack) : Prop :=
  FSCLOSED F1 /\ FSCLOSED F2 /\
  forall m (Hmn : m <= n) v1 v2,
    Vrel m Hmn v1 v2 ->
    | F1, v1 | m ↓ -> | F2, v2 | ↓.

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                   (e1 e2 : Exp)
                 : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall m (Hmn : m <= n) F1 F2,
     frame_rel m (fun m' H => Vrel m' (Nat.le_trans _ _ _ H Hmn)) F1 F2 ->
     | F1, e1 | m ↓ -> | F2, e2 | ↓
.

Definition Vrel_rec (n : nat)
                    (Vrel : forall m, m < n -> Exp -> Exp -> Prop)
                    (v1 v2 : Exp) : Prop :=
  VALCLOSED v1 /\ VALCLOSED v2 /\
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => 
    if length vl1 =? length vl2 then
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 ->
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                 (b1.[list_subst vals1 idsubst])
                 (b2.[list_subst vals2 idsubst])
    else False
  | ERecFun f1 vl1 b1, ERecFun f2 vl2 b2 =>
    if length vl1 =? length vl2 then
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 ->
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                 (b1.[list_subst (ERecFun f1 vl1 b1 :: vals1) idsubst])
                 (b2.[list_subst (ERecFun f2 vl2 b2 :: vals2) idsubst])
     else False
  | _, _ => False
  end
.

Definition Vrel : nat -> Exp -> Exp -> Prop :=
  Fix Wf_nat.lt_wf _ Vrel_rec.

Definition Erel (n : nat) (e1 e2 : Exp) : Prop :=
  exp_rel n (fun m _ => Vrel m) e1 e2.


Definition Frel (n : nat) (K1 K2 : FrameStack) : Prop :=
  frame_rel n (fun m _ => Vrel m) K1 K2.

(** ξ and η assigns closed expressions to vars in Γ 
  Basically this says, ξ and η are equivalent pointwise for Γ
*)

Lemma Vrel_rec_pointwise {n : nat} :
  forall (f g : forall m : nat, (m < n)%nat -> Exp -> Exp -> Prop),
    (forall (m : nat) (p : (m < n)%nat), f m p = g m p) ->
    Vrel_rec n f = Vrel_rec n g.
Proof.
  intros.
  unfold Vrel_rec.
  extensionality v1.
  extensionality v2.
  destruct v1, v2; auto. break_match_goal. 2: auto.
  f_equal. f_equal.
  extensionality m.
  extensionality Hmn.
  extensionality v1'.
  extensionality v2'.
  rewrite H.
  extensionality l1. extensionality l2.
  extensionality x.
  f_equal.
  extensionality m'.
  extensionality H0.
  trivial.
  
  f_equal. f_equal.
  break_match_goal; auto. extensionality m.
  extensionality Hmn.
  extensionality v1'.
  extensionality v2'.
  rewrite H.
  extensionality l1. extensionality l2.
  extensionality x.
  f_equal.
  extensionality m'.
  extensionality H0.
  trivial.
Qed.

Lemma Vrel_Fix_eq : forall {n : nat} {v1 v2 : Exp},
  Vrel n v1 v2
  = 
  Vrel_rec n (fun (m : nat) (_ : m < n) => Vrel m) v1 v2.
Proof.
  intros.
  unfold Vrel.
  rewrite Fix_eq by (auto using Vrel_rec_pointwise).
  trivial.
Qed.

Section Tests.

  Local Definition e1 := ELit 0.
  Local Definition e2 := EFun [] e1.
  Local Definition e3 := EFun [] (EPlus e1 e1).
  Local Definition inf f := EApp (ERecFun f [] (EApp (EFunId 0 f) [])) [].

  Axiom inf_diverges : forall f clock, eval clock (inf f) = Timeout.

  Goal Erel 0 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor. intros.
    destruct H, H1. eapply H2; eauto. rewrite Vrel_Fix_eq. unfold e1, Vrel_rec. repeat constructor.
  Qed.
  
  Goal Erel 3 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor. intros.
    destruct H, H1. eapply H2; eauto. rewrite Vrel_Fix_eq. unfold e1, Vrel_rec. repeat constructor.
  Qed.
  
  Goal Erel 3 e2 e2.
  Proof.
    split. 2: split.
    1-2: repeat constructor. intros.
    destruct H, H1. eapply H2; eauto. rewrite Vrel_Fix_eq. unfold e1, Vrel_rec. repeat constructor.
    apply length_zero_iff_nil in H3. apply length_zero_iff_nil in H4. subst. intros. cbn. cbn in H4.
    destruct H3, H6. eapply H7; eauto. rewrite Vrel_Fix_eq. unfold e1, Vrel_rec. repeat constructor.
  Qed.

  Goal Erel 3 e2 e3.
  Proof.
    split. 2: split.
    1-2: repeat constructor. intros.
    destruct H, H1. eapply H2; eauto. rewrite Vrel_Fix_eq. unfold e1, Vrel_rec. repeat constructor.
    apply length_zero_iff_nil in H3. apply length_zero_iff_nil in H4. subst. intros. cbn. cbn in H4.
    destruct H3, H6. epose (H7 m1 _ (ELit 0) (ELit 0) _ H4).
    destruct t. exists (S (S (S x))). constructor. econstructor. constructor.
    constructor. assumption.
    Unshelve.
    all: repeat constructor.
  Qed.

End Tests.

Scheme le_dep_ind := Induction for le Sort Prop.

Lemma Vrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    Vrel m v1 v2.
Proof.
  induction 1 using le_dep_ind;
    intros;
    eauto.
  rewrite Vrel_Fix_eq.
  rewrite Vrel_Fix_eq in H.
  unfold Vrel_rec at 1.
  unfold Vrel_rec at 1 in H.
  destruct v1, v2; intuition; break_match_hyp; intros.
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e. contradiction.
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e. contradiction.
  Unshelve. all: lia.
Qed.

Lemma Erel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Exp},
    Erel n e1 e2 ->
    Erel m e1 e2.
Proof.
  intros.
  unfold Erel, exp_rel.
  unfold Erel, exp_rel in H.
  destruct H, H0. split; auto. split; auto.
  intros. eapply (H1 m0); eauto. lia.
Qed.

Lemma Vrel_closed : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v1 /\ VALCLOSED v2.
Proof.
  intros.
  destruct H as [? [? ?] ].
  destruct v1, v2; intuition.
Qed.

Lemma Vrel_closed_l : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v1.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Global Hint Resolve Vrel_closed_l : core.

Lemma Vrel_closed_r : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v2.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Global Hint Resolve Vrel_closed_r : core.

Lemma Erel_closed : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros.
  unfold Erel, exp_rel in H.
  intuition.
Qed.

Lemma Erel_closed_l : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Global Hint Resolve Erel_closed_l : core.

Lemma Erel_closed_r : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Global Hint Resolve Erel_closed_r : core.

(* Def: closed values are related *)
Definition Grel (n : nat) (Γ : nat) (ξ₁ ξ₂ : Substitution) : Prop :=
  SUBSCOPE Γ ⊢ ξ₁ ∷ 0 /\ SUBSCOPE Γ ⊢ ξ₂ ∷ 0 /\
  forall x, x < Γ -> 
    match (ξ₁ x), (ξ₂ x) with
    | inl e1, inl e2 => Vrel n e1 e2
(*     | inr n1, inr n2 => n1 = n2 NOTE: these are not needed, because of the subscoped property
    | inr n1, inl (EVar n2 f) => n1 = n2
    | inr n1, inl (EFunId n2 f) => n1 = n2
    | inl (EVar n2 f), inr n1 => n2 = n1
    | inl (EFunId n2 f), inr n1 => n2 = n1 *)
    | _, _ => False
    end.


(** Closing substitutions  *)

(* Definition Grel (n : nat) (Γ : nat) (ξ η : VarFunId -> Exp) : Prop :=
  (subscoped Γ [] ξ) /\
  (subscoped Γ [] η) /\
  forall x, In x Γ -> Vrel n (ξ x) (η x). *)

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

Lemma Grel_downclosed_helper : forall vals1 vals2 m n,
  m <= n -> length vals1 = length vals2 ->
  list_biforall (Vrel n) vals1 vals2 ->
  list_biforall (Vrel m) vals1 vals2.
Proof.
  intro. induction vals1 using list_length_ind; intros.
  destruct vals1, vals2.
  * constructor.
  * inversion H1.
  * inversion H1.
  * inversion H2. subst. constructor. 
    - eapply Vrel_downclosed. eauto.
    - eapply H; eauto.
Unshelve. auto.
Qed.

Lemma Grel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {Γ : nat} {ξ₁ ξ₂ : Substitution},
    Grel n Γ ξ₁ ξ₂ ->
    Grel m Γ ξ₁ ξ₂ .
Proof.
  unfold Grel; intros.
  unfold Grel; intros. intuition.
  repeat break_match_goal; specialize (H2 x H1); try rewrite Heqs in H2; try rewrite Heqs0 in H2; [ intuition (eauto using Vrel_downclosed) | contradiction | contradiction ].
Qed.

Definition Vrel_open (Γ : nat) (e1 e2 : Exp) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Vrel n (subst ξ₁ e1) (subst ξ₂ e2).

Definition Erel_open (Γ : nat) (e1 e2 : Exp) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Erel n (subst ξ₁ e1) (subst ξ₂ e2).

(* Lemma subscoped_to_vrel vals :
  subscoped [] vals ->
  list_biforall (Vrel 0) vals vals.
Proof.
  induction vals; intros; constructor.
  - rewrite Vrel_Fix_eq. specialize (H 0 (Nat.lt_0_succ _)). simpl in H.
    unfold Vrel_rec. destruct H.
    all: intuition.
    all: try constructor.
    all: auto.
    + break_match_goal. 2: congruence.
      intros. inversion Hmn.
    + break_match_goal. 2: congruence.
      intros. inversion Hmn.
  - apply IHvals. intro. intros. apply (H (S i)). simpl. lia.
Qed. *)

Lemma Erel_open_closed : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
              EXPCLOSED (subst ξ e1) /\ EXPCLOSED (subst ξ e2).
Proof.
  intros.
  apply @Erel_closed with (n:=0).
  apply H; auto.
  unfold Grel.
  intuition idtac. break_match_goal.
  rewrite Vrel_Fix_eq. unfold Vrel_rec at 1.
  specialize (H0 x H1) as P'. rewrite Heqs in P'.
  * destruct P'; intuition; cbn; try constructor; auto. inversion H2. inversion H2.
    1-2: break_match_goal; intros; try congruence; try inversion Hmn. 1-2: rewrite Nat.eqb_refl in Heqb; congruence.
  * specialize (H0 x H1). rewrite Heqs in H0. lia.
Qed.

Lemma Erel_open_scope : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  pose proof (Erel_open_closed H).
  split;
  eapply (subst_implies_scope_exp); intros; apply H0; auto.
Qed.

Lemma Erel_open_scope_l : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros. eapply Erel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Erel_open_scope_l : core.

Lemma Erel_open_scope_r : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros. eapply Erel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Erel_open_scope_r : core.

Lemma Vrel_possibilities : forall {n v1 v2},
  Vrel n v1 v2 ->
  (exists n, v1 = ELit n /\ v2 = ELit n) \/
  (exists vl1 vl2 b1 b2, v1 = EFun vl1 b1 /\ v2 = EFun vl2 b2) \/
  (exists f1 f2 vl1 vl2 b1 b2, v1 = ERecFun f1 vl1 b1 /\ v2 = ERecFun f2 vl2 b2).
Proof.
  intros; destruct v1, v2; destruct H as [? [? ?] ]; subst; try contradiction.
  * left. eexists; split; reflexivity.
  * right. left. repeat eexists.
  * right. right. repeat eexists.
Qed.

Lemma Vrel_open_closed : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
              VALCLOSED (subst ξ e1) /\ VALCLOSED (subst ξ e2).
Proof.
  intros.
  apply @Vrel_closed with (n:=0).
  apply H; auto.
  unfold Grel.
  intuition idtac. break_match_goal.
  rewrite Vrel_Fix_eq. unfold Vrel_rec at 1.
  specialize (H0 x H1) as P'. rewrite Heqs in P'.
  * destruct P'; intuition; cbn; try constructor; auto. inversion H2. inversion H2.
    1-2: break_match_goal; intros; try congruence; try inversion Hmn. 1-2: rewrite Nat.eqb_refl in Heqb; congruence.
  * specialize (H0 x H1). rewrite Heqs in H0. lia.
Qed.

Lemma Vrel_open_scope : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e1 /\ VAL Γ ⊢ e2.
Proof.
  intros.
  pose proof (Vrel_open_closed H).
  split;
  eapply (subst_implies_scope_val); intros; apply H0; auto.
Qed.

Lemma Vrel_open_scope_l : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e1.
Proof.
  intros. eapply Vrel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Vrel_open_scope_l : core.

Lemma Vrel_open_scope_r : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e2.
Proof.
  intros. eapply Vrel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Vrel_open_scope_r : core.

Lemma Frel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    Frel m F1 F2.
Proof.
  unfold Frel, frame_rel.
  intuition. eapply H2 in H3. exact H3. lia. auto.
Qed.

Global Hint Resolve Frel_downclosed : core.

Lemma Frel_closed : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F1 /\ FSCLOSED F2.
Proof.
  intros.
  unfold Frel, frame_rel in H.
  intuition.
Qed.

Lemma Frel_closed_l : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F1.
Proof.
  intros.
  apply Frel_closed in H.
  intuition.
Qed.

Global Hint Resolve Frel_closed_l : core.

Lemma Frel_closed_r : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F2.
Proof.
  intros.
  apply Frel_closed in H.
  intuition.
Qed.

Global Hint Resolve Frel_closed_r : core.


Lemma biforall_vrel_scoped : forall vals1 vals2 Γ,
  list_biforall (Vrel_open Γ) vals1 vals2 ->
  Forall (fun e => VAL Γ ⊢ e) vals1 /\ Forall (fun e => VAL Γ ⊢ e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; repeat constructor.
  * eapply Vrel_open_scope_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Vrel_open_scope_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_erel_scoped : forall vals1 vals2 Γ,
  list_biforall (Erel_open Γ) vals1 vals2 ->
  Forall (fun e => EXP Γ ⊢ e) vals1 /\ Forall (fun e => EXP Γ ⊢ e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; split; constructor.
  * eapply Erel_open_scope_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Erel_open_scope_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_vrel_closed : forall vals1 vals2 m,
  list_biforall (Vrel m) vals1 vals2 ->
  Forall (fun e => VALCLOSED e) vals1 /\ Forall (fun e => VALCLOSED e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; repeat constructor.
  * eapply Vrel_closed_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Vrel_closed_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_erel_closed : forall vals1 vals2 m,
  list_biforall (Erel m) vals1 vals2 ->
  Forall (fun e => EXPCLOSED e) vals1 /\ Forall (fun e => EXPCLOSED e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; split; constructor.
  * eapply Erel_closed_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Erel_closed_r; eauto.
  * eapply IHvals1; eauto.
Qed.

(* Theorem Erel_open_trans :
  forall Γ, Transitive (Erel_open Γ).
Proof.
  repeat intro. unfold Erel_open in H, H0.

Theorem Vrel_open_trans :
  forall Γ, Transitive (Vrel_open Γ).
Proof.
  repeat intro. unfold Vrel_open in *.

Theorem Erel_open_trans : *)