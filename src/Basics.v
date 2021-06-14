Require Export Coq.micromega.Lia
               Coq.Lists.List.
Import ListNotations.

Theorem indexed_to_forall {A : Type} (l : list A) : forall P def,
  Forall P l
<->
  (forall i, i < Datatypes.length l -> P (nth i l def)).
Proof.
  induction l; split; intros.
  * inversion H0.
  * constructor.
  * inversion H. subst. destruct i.
    - simpl. auto.
    - simpl. apply IHl. exact H4. simpl in H0. lia.
  * constructor.
    - apply (H 0). simpl. lia.
    - eapply IHl. intros. apply (H (S i)). simpl. lia.
Qed.

Lemma element_exist {A : Type} : forall n (l : list A), S n = Datatypes.length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Theorem map_id {T} : forall (l : list T), List.map id l = l.
Proof.
  induction l; simpl; try rewrite IHl; auto.
Qed.

Theorem last_element_exists {T} :
  forall (l: list T) n, S n = Datatypes.length l -> exists l' x, l = l' ++ [x].
Proof.
  induction l; intros.
  * inversion H.
  * inversion H. destruct l.
    - exists [], a. reflexivity.
    - simpl in H1. epose (IHl (pred n) _). destruct e, H0. subst. rewrite H0.
      exists (a::x), x0. apply app_comm_cons. Unshelve. simpl. lia.
Qed.

Inductive list_biforall {T1 T2 : Type} (P : T1 -> T2 -> Prop) : list T1 -> list T2 -> Prop :=
| biforall_nil : list_biforall P [] []
| biforall_cons hd hd' tl tl' : P hd hd' -> list_biforall P tl tl' -> list_biforall P (hd::tl) (hd'::tl').

Theorem indexed_to_biforall {T1 T2 : Type} : forall (P : T1 -> T2 -> Prop) (l1 : list T1) (l2 : list T2) (d1 : T1) (d2 : T2),
   list_biforall P l1 l2 <-> (forall i, i < length l1 -> P (nth i l1 d1) (nth i l2 d2)) /\ length l1 = length l2.
Proof.
  split; intros.
  * induction H.
    - split; intros; auto. inversion H.
    - destruct IHlist_biforall. split. 2: simpl; lia. destruct i; intros.
      + exact H.
      + apply H1. simpl in H3. lia.
  * destruct H. revert H0 H. generalize dependent l2. generalize dependent d1.
    generalize dependent d2. induction l1; intros.
    - simpl in H0. apply eq_sym, length_zero_iff_nil in H0. subst. constructor.
    - simpl in H0. apply element_exist in H0 as G. destruct G, H1. subst. inversion H0.
      constructor. apply (H 0); simpl; lia. eapply IHl1; auto. intros. apply (H (S i)).
      simpl. lia.
Qed.