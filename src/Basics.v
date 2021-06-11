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