
Require Export Coq.FSets.FMapList
               Coq.Structures.OrderedTypeEx
               Coq.Structures.OrderedType
               Coq.Classes.EquivDec.
From Coq Require Export Strings.String.
From Coq Require Export micromega.Lia.
From Coq Require Export Arith.PeanoNat.

Definition Var : Set := string.
Definition FunctionIdentifier : Set := string * nat.

Definition VarFunId : Set := Var + FunctionIdentifier.

(* Section Basic_Eq_Dec.
(** Decidable equality for product and sum types *)
  Context {A B : Type}.

  Hypothesis A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Hypothesis B_eq_dec : forall b1 b2 : B, {b1 = b2} + {b1 <> b2}.

  Proposition prod_eq_dec : forall p1 p2 : A * B, {p1 = p2} + {p1 <> p2}.
  Proof.
    set (eq1 := A_eq_dec).
    set (eq2 := B_eq_dec).
    decide equality.
  Defined.

  Proposition sum_eq_dec : forall p1 p2 : A + B, {p1 = p2} + {p1 <> p2}.
  Proof.
    set (eq1 := A_eq_dec).
    set (eq2 := B_eq_dec).
    decide equality.
  Defined.

End Basic_Eq_Dec. *)

Module VarFunid_as_OT <: UsualOrderedType.

  Definition t := VarFunId.

  Definition eq := @eq VarFunId.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Inductive ltvarfid : VarFunId -> VarFunId -> Prop :=
    | lt_var : forall v1 v2, String_as_OT.lt v1 v2 -> ltvarfid (inl v1) (inl v2)
    | lt_var_funid : forall v f, ltvarfid (inl v) (inr f)
    | lt_funid_name : forall s s' n n', String_as_OT.lt s s' -> ltvarfid (inr (s, n)) (inr (s', n'))
    | lt_funid_arit : forall s n n', n < n' -> ltvarfid (inr (s, n)) (inr (s, n'))
  .

  Definition lt := ltvarfid.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros. inversion H.
    * inversion H0; constructor.
      subst. eapply String_as_OT.lt_trans. exact H1. inversion H5. subst. auto.
    * inversion H0; constructor. subst. inversion H4.
    * inversion H0; subst; try congruence.
      - inversion H5. subst. constructor. eapply String_as_OT.lt_trans. exact H1. auto.
      - inversion H5. subst. constructor. auto.
    * inversion H0; subst; try congruence.
      - inversion H5. subst. constructor. auto.
      - inversion H5. subst. apply lt_funid_arit. lia.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold not. intros. inversion H0. subst. inversion H.
    * subst. eapply String_as_OT.lt_not_eq. apply H3. constructor.
    * subst. eapply String_as_OT.lt_not_eq. apply H3. constructor.
    * subst. lia.
  Qed.

  Definition cmp (a b : VarFunId) : comparison :=
    match a, b with
    | inl v, inl v' => String_as_OT.cmp v v'
    | inl _, inr _ => Lt
    | inr _, inl _ => Gt
    | inr (s, n), inr (s', n') =>
        match String_as_OT.cmp s s' with
        | Eq => Nat.compare n n'
        | r => r
        end
    end.

  Lemma cmp_eq (a b : VarFunId):
    cmp a b = Eq  <->  a = b.
  Proof.
    split; intros; destruct a, b; inversion H.
    * apply String_as_OT.cmp_eq in H1. subst. auto.
    * destruct f. inversion H1.
    * destruct f, f0. simpl in H. destruct (String_as_OT.cmp s s0) eqn:P; try congruence.
      apply String_as_OT.cmp_eq in P. apply Nat.compare_eq in H. subst. auto.
    * simpl. apply String_as_OT.cmp_eq. auto.
    * simpl. destruct f0. destruct (String_as_OT.cmp s s) eqn:P.
      apply Nat.compare_refl.
      - eapply String_as_OT.cmp_lt in P. apply String_as_OT.lt_not_eq in P.
        exfalso. apply P. constructor.
      - rewrite String_as_OT.cmp_antisym in P. unfold CompOpp in P.
        destruct (String_as_OT.cmp s s) eqn:P0; try congruence.
        eapply String_as_OT.cmp_lt in P0. apply String_as_OT.lt_not_eq in P0.
        exfalso. apply P0. constructor.
  Qed.

  Lemma cmp_antisym (a b : VarFunId):
    cmp a b = CompOpp (cmp b a).
  Proof.
    (* revert b.
    induction a, b; try easy.
    cbn. rewrite IHa. clear IHa.
    remember (Ascii_as_OT.cmp _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; rewrite Ascii_as_OT.cmp_antisym in Heqc;
      destruct Ascii_as_OT.cmp; cbn in *; easy. *)
  Admitted.

  Lemma cmp_lt (a b : VarFunId):
    cmp a b = Lt  <->  lt a b.
  Proof.
    (* revert b.
    induction a as [ | a_head a_tail ], b; try easy; cbn.
    { split; trivial. intro. apply lts_empty. }
    remember (Ascii_as_OT.cmp _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; split; intro H; try discriminate; trivial.
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      apply String_as_OT.lts_tail.
      apply IHa_tail.
      assumption.
    }
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      inversion H; subst. { rewrite IHa_tail. assumption. }
      exfalso. apply (Nat.lt_irrefl (nat_of_ascii a)). assumption.
    }
    {
      apply String_as_OT.lts_head.
      rewrite<- Ascii_as_OT.cmp_lt_nat.
      assumption.
    }
    {
      exfalso. inversion H; subst.
      {
         assert(X: Ascii_as_OT.cmp a a = Eq). { apply Ascii_as_OT.cmp_eq. trivial. }
         rewrite Heqc in X. discriminate.
      }
      rewrite<- Ascii_as_OT.cmp_lt_nat in *. rewrite Heqc in *. discriminate.
    } *)
  Admitted.


  Local Lemma compare_helper_lt {a b : VarFunId} (L : cmp a b = Lt):
    lt a b.
  Proof.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_gt {a b : VarFunId} (G : cmp a b = Gt):
    lt b a.
  Proof.
    rewrite cmp_antisym in G.
    rewrite CompOpp_iff in G.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_eq {a b : VarFunId} (E : cmp a b = Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.




  Definition compare (a b : VarFunId) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT (compare_helper_lt E)
    | Gt => fun E => GT (compare_helper_gt E)
    | Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.


  Definition eq_dec (x y : VarFunId): {x = y} + { ~ (x = y)} := sum_eqdec string_dec (prod_eqdec string_dec Nat.eq_dec) x y.

End VarFunid_as_OT.

Module Import Environment := FMapList.Make(VarFunid_as_OT).

Check Environment.MapsTo.
Check Environment.MapsTo _ (inl "a"%string) (Environment.empty _).
Import Environment.
Compute add (inl "a"%string) 1 (Environment.empty _).
