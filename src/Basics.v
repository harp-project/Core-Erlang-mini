Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.
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

Theorem biforall_length :
  forall {T1 T2 : Type} (es : list T1) (es' : list T2) P, list_biforall P es es' -> length es = length es'.
Proof.
  intros. induction H; auto. simpl. auto.
Qed.

Lemma biforall_impl : forall {T1 T2} (l1 : list T1) (l2 : list T2) (P Q : T1 -> T2 -> Prop),
  (forall x y, P x y -> Q x y) ->
  list_biforall P l1 l2 -> list_biforall Q l1 l2.
Proof.
  induction l1; intros; inversion H0; constructor; subst.
  now apply H.
  eapply IHl1; eauto.
Qed.

Lemma biforall_app : forall {T1 T2} (l1 l1' : list T1) (l2 l2' : list T2) P,
  list_biforall P l1 l2 -> list_biforall P l1' l2'
->
  list_biforall P (l1 ++ l1') (l2 ++ l2').
Proof.
  induction l1; intros.
  * inversion H. auto.
  * inversion H. subst. do 2 rewrite <- app_comm_cons. constructor; auto. 
Qed.

Lemma biforall_map :
  forall {T1 T2 T1' T2'} l l' f1 f2 (P : T1 -> T2 -> Prop) (Q : T1' -> T2' -> Prop), list_biforall P l l' ->
  (forall x y, P x y -> Q (f1 x) (f2 y))
->
  list_biforall Q (map f1 l) (map f2 l').
Proof.
  induction l; intros; inversion H; simpl; constructor; subst.
  * inversion H. subst. apply H0; auto.
  * eapply IHl; eauto.
Qed.

Lemma biforall_forall_refl : forall {T} (l: list T) P, list_biforall P l l -> Forall (fun x => P x x) l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.

Lemma forall_biforall_refl : forall {T} (l: list T) P, Forall (fun x => P x x) l -> list_biforall P l l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.

Lemma nth_possibilities {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.

Lemma nth_possibilities_alt {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2 /\ i >= length l1.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.