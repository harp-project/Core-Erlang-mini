Require Export Scoping.

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

(* I think this definition is not suitable for equivalence:
  - forall v1 v2, which are equivalent:
  e.g. fun() -> 1 ~ fun() -> 1 iff
  forall v1 ~ v2, where `eval fun() -> 1 = v1` (i.e. `v1 = fun() -> 1`) implies `eval fun() -> 1 = v2`
     that means, v2 = fun() -> b, where `eval b = 1`
     This does NOT imply, that `b = 1`, it could be `b = (fun() -> 1)()` too for example

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                   (e1 e2 : Exp)
                 : Prop :=
  (* closed e1 /\ closed e2 /\ *)
  forall m (Hmn : m <= n) v1 v2,
    (Vrel m Hmn v1 v2 /\ (* maybe -> ? *)
     eval m e1 = Res v1) -> (exists clock, eval clock e2 = Res v2)
. *)

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Exp -> Exp -> Prop)
                   (e1 e2 : Exp)
                 : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall m (Hmn : m <= n) v1,
     eval m e1 = Res v1 -> (exists v2, (exists clock, eval clock e2 = Res v2) /\ Vrel m Hmn v1 v2)
.

Inductive list_biforall {T : Type} (P : T -> T -> Prop) : list T -> list T -> Prop :=
| biforall_nil : list_biforall P [] []
| biforall_cons hd hd' tl tl' : P hd hd' -> list_biforall P tl tl' -> list_biforall P (hd::tl) (hd'::tl').

Check list_eq_dec. Print sumbool.

Definition Vrel_rec (n : nat)
                    (Vrel : forall m, m < n -> Exp -> Exp -> Prop)
                    (v1 v2 : Exp) : Prop :=
  VALCLOSED v1 /\ VALCLOSED v2 /\
  match v1, v2 with
  | ELit l1, ELit l2 => l1 = l2
  | EFun vl1 b1, EFun vl2 b2 => 
    match list_eq_dec string_dec vl1 vl2 with
    | right _ => False
    | left _ => 
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 -> (* With DB indices, this could be removed *)
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                                                   (subst (idsubst[[::= combine (map inl vl1) vals1 ]]) b1)
                                                   (subst (idsubst[[::= combine (map inl vl2) vals2 ]]) b2)
    end
  | ERecFun f1 vl1 b1, ERecFun f2 vl2 b2 =>
    match list_eq_dec string_dec vl1 vl2 with
    | right _ => False
    | left _ => 
     forall m (Hmn : m < n), forall (vals1 vals2 : list Exp),
       length vals1 = length vl1 -> length vals2 = length vl2 ->
       list_biforall (Vrel m Hmn) vals1 vals2 
     ->
       exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn)) 
                 (subst (idsubst[[::= combine ((inr f1) :: map inl vl1) ((ERecFun f1 vl1 b1) :: vals1)]]) b1)
                 (subst (idsubst[[::= combine ((inr f2) :: map inl vl2) ((ERecFun f2 vl2 b2) :: vals2)]]) b2)
    end
  | _, _ => False
  end
.

Definition Vrel : nat -> Exp -> Exp -> Prop :=
  Fix Wf_nat.lt_wf _ Vrel_rec.

Definition Erel (n : nat) (e1 e2 : Exp) : Prop :=
  exp_rel n (fun m _ => Vrel m) e1 e2.

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
  Local Definition inf f := EApp (ERecFun f [] (EApp (EFunId f) [])) [].

  Axiom inf_diverges : forall f clock, eval clock (inf f) = Timeout.

  Goal Erel 0 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e1. split.
    * destruct m; inversion H; inversion Hmn.
    * inversion Hmn. subst. inversion H.
  Qed.
  
  Goal Erel 3 e1 e1.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e1. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H.
      split; try split; try constructor.
  Qed.
  
  Goal Erel 3 e2 e2.
  Proof.
    split. 2: split.
    1-2: repeat constructor.
    exists e2. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H. subst. rewrite Vrel_Fix_eq.
      split; try split; repeat constructor.
      simpl.
      intros. apply length_zero_iff_nil in H0. apply length_zero_iff_nil in H1. subst.
      exists e1. split.
      - exists 1. reflexivity.
      - destruct m1; inversion H3. subst.
        split; try split; try constructor.
  Qed.
  
  Goal Erel 3 e2 e3.
  Proof.
    split; try split.
    1-2: repeat constructor.
    exists e3. split.
    * destruct m; inversion H. exists 1. reflexivity.
    * destruct m; inversion H. subst. rewrite Vrel_Fix_eq.
      split; try split; repeat constructor.
      simpl.
      intros. apply length_zero_iff_nil in H0. apply length_zero_iff_nil in H1. subst.
      exists e1. split.
      - exists 3. reflexivity.
      - destruct m1; inversion H3. subst.
        split; try split; repeat constructor.
  Qed.

End Tests.

Scheme le_dep_ind := Induction for le Sort Prop.
Check le_dep_ind. 

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
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e0. contradiction.
  epose (H2 m1 _ vals1 vals2 H1 H3 H4). apply e0. contradiction.
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

Hint Resolve Vrel_closed_l.

Lemma Vrel_closed_r : forall {n : nat} {v1 v2 : Exp},
    Vrel n v1 v2 ->
    VALCLOSED v2.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Hint Resolve Vrel_closed_r.

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

Hint Resolve Erel_closed_l.

Lemma Erel_closed_r : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Hint Resolve Erel_closed_r.

(*
Definition subscoped (l l' : list VarFunId) (ξ : VarFunId -> Exp) : Prop :=
  forall v, In v l -> ValScoped l' (ξ v).

Notation "'SUBSCOPE' Γ ⊢ ξ :: Γ'" := (subscoped Γ Γ' ξ) (at level 69, ξ at level 99, no associativity).
*)

(* Def: closed values are related *)
Definition Grel (n : nat) (Γ : list VarFunId) (ξ₁ ξ₂ : Substitution) : Prop :=
  subscoped Γ [] ξ₁ /\ subscoped Γ [] ξ₂ /\
  forall x, In x Γ -> Vrel n (ξ₁ x) (ξ₂ x).


(** Closing substitutions  *)

(* Definition Grel (n : nat) (Γ : list VarFunId) (ξ η : VarFunId -> Exp) : Prop :=
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
  forall {n m : nat} {Hmn : m <= n} {Γ : list VarFunId} {ξ₁ ξ₂ : Substitution},
    Grel n Γ ξ₁ ξ₂ ->
    Grel m Γ ξ₁ ξ₂ .
Proof.
  unfold Grel; intros; intuition (eauto using Vrel_downclosed).
Qed.

Definition Vrel_open (Γ : list VarFunId) (e1 e2 : Exp) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Vrel n (subst ξ₁ e1) (subst ξ₂ e2).

Definition Erel_open (Γ : list VarFunId) (e1 e2 : Exp) :=
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
    forall ξ, subscoped Γ [] ξ ->
              EXPCLOSED (subst ξ e1) /\ EXPCLOSED (subst ξ e2).
Proof.
  intros.
  apply @Erel_closed with (n:=0).
  apply H; auto.
  unfold Grel.
  intuition idtac.
  rewrite Vrel_Fix_eq. unfold Vrel_rec at 1.
  pose (P := H0 x H1). destruct P; intuition; try constructor; auto.
  1-2: break_match_goal; intros; try congruence; inversion Hmn.
Qed.

Lemma Erel_open_scope : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  pose proof (Erel_open_closed H).
  split;
  eapply (sub_implies_scope_exp); intros; apply H0; auto.
Qed.

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

