Require Export ConcurrentProperties.
Import ListNotations.

Definition strong_bisimulation (R : Node -> Node -> Prop) :=
  (forall p q p' a ι, R p q -> p -[a | ι]ₙ-> p' -> exists q', q -[a | ι]ₙ-> q' /\ R p' q') /\
  (forall p q q' a ι, R p q -> q -[a | ι]ₙ-> q' -> exists p', p -[a | ι]ₙ-> p' /\ R p' q').

Theorem eq_is_strong_bisim :
  strong_bisimulation eq.
Proof.
  split; intros.
  {
    subst. induction H0.
    * eexists. split. 2: reflexivity.
      eapply n_send; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_arrive; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_other; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_spawn; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_terminate.
  }
  {
    subst. induction H0.
    * eexists. split. 2: reflexivity.
      eapply n_send; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_arrive; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_other; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_spawn; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply n_terminate.
  }
Qed.




(** Lanese et. al.:  *)
(* Definition ppid (n : Node) : list PID := map fst n. *)
(*
Fixpoint expPids (e : Exp) : list PID :=
match e with
 | ELit l => []
 | EPid p => [p]
 | EVar n => []
 | EFunId n => []
 | EFun vl e => expPids e
 | EApp exp l => expPids exp ++ fold_right (fun x acc => expPids x ++ acc) [] l
 | ELet v e1 e2 => expPids e1 ++ expPids e2
 | ELetRec f vl b e => expPids b ++ expPids e
 | EPlus e1 e2 => expPids e1 ++ expPids e2
 | ECase e p e1 e2 => expPids e ++ expPids e1 ++ expPids e2
 | ECons e1 e2 => expPids e1 ++ expPids e2
 | ENil => []
 | VCons e1 e2 => expPids e1 ++ expPids e2
 | ESend p e => expPids p ++ expPids e
 | EReceive l => fold_right (fun x acc => expPids (snd x) ++ acc) [] l
 | ESelf => []
 | ESpawn e1 e2 => expPids e1 ++ expPids e2
end.

Definition framePids (f : Frame) : list PID :=
match f with
 | FApp1 l => fold_right (fun x acc => expPids x ++ acc) [] l
 | FApp2 v l1 l2 => expPids v ++
                    fold_right (fun x acc => expPids x ++ acc) [] l1 ++ 
                    fold_right (fun x acc => expPids x ++ acc) [] l2
 | FLet v e2 => expPids e2
 | FPlus1 e2 => expPids e2
 | FPlus2 v => expPids v
 | FCase p e2 e3 => expPids e2 ++ expPids e3
 | FCons1 e1 => expPids e1
 | FCons2 v2 => expPids v2
 | FSend1 e => expPids e
 | FSend2 p => expPids p
 | FSpawn1 e => expPids e
 | FSpawn2 p => expPids p
end.

Definition mailboxPids (m : Mailbox) : list PID := fold_right (fun x acc => expPids x ++ acc) [] m.
Definition frameStackPids (fs : FrameStack) : list PID := fold_right (fun x acc => framePids x ++ acc) [] fs.
Definition processPids (p : Process) : list PID := 
match p with
| (fs, e, m) => frameStackPids fs ++ expPids e ++ mailboxPids m
end.
Definition usedPids (n : Node) : list PID :=
  fold_right (fun '(_, p) acc => processPids p ++ acc) [] n.
Search In. Print in_list.
Definition untakenPids (n : Node) : list PID :=
  filter (fun e => in_list _ Nat.eqb e (ppid n)) (usedPids n).

Definition pidCompatibleNode (n1 n2 : Node) :=
  Forall (fun e => ~In e (ppid n2)) (untakenPids n1) /\
  Forall (fun e => ~In e (ppid n1)) (untakenPids n2).
Definition pidCompatibleRelation (R : Node -> Node -> Prop) :=
  forall n1 n2, R n1 n2 -> pidCompatibleNode n1 n2.
Definition pidCompatibleReduction A A' B B' a b ι ι2 (r1 : A -[a|ι]ₙ-> A') (r2 : B -[b|ι2]ₙ-> B') := 
pidCompatibleNode A A' /\ .

*)


(** Not too good definition
  -->* cannot be proved to be a bisimulation, because of AInternal ordering
*)
(* Definition weak_bisimulation (R : Node -> Node -> Prop) :=
  (forall p q p' a ι, R p q -> p -[a | ι]ₙ-> p' ->
     exists q', onlyOne a ι q q' /\ R p' q') /\
  (forall p q q' a ι, R p q -> q -[a | ι]ₙ-> q' ->
     exists p', onlyOne a ι p p' /\ R p' q'). *)

(** restriction, no internal actions investigated *)
Definition weak_bisimulation (R : Node -> Node -> Prop) :=
  (forall p q p' a ι, a <> AInternal ->
     R p q -> p -[a | ι]ₙ-> p' ->
     exists q', onlyOne a ι q q' /\ R p' q') /\
  (forall p q q' a ι, a <> AInternal ->
     R p q -> q -[a | ι]ₙ-> q' ->
     exists p', onlyOne a ι p p' /\ R p' q').

Definition Node_equivalence (n1 n2 : Node) := exists R, weak_bisimulation R /\ R n1 n2.

Lemma strong_bisim_is_weak : forall R, strong_bisimulation R -> weak_bisimulation R.
Proof.
  unfold strong_bisimulation, weak_bisimulation; intros. destruct H. split.
  * intros. eapply H in H3. 2: exact H2. destruct H3 as [q' [H3_1 H3_2]].
    exists q'. split; auto. exists q, q'. split. 2: split. 2: auto.
    all: exists [], 0; split; [constructor | constructor ]; auto.
  * intros. eapply H0 in H3. 2: exact H2. destruct H3 as [p' [H3_1 H3_2]].
    exists p'. split; auto. exists p, p'. split. 2: split. 2: auto.
    all: exists [], 0; split; [constructor | constructor ]; auto.
Qed.

Theorem internalSteps_weak_bisim : weak_bisimulation internals.
Proof.
 split; intros.
  * unfold onlyOne.
    destruct H0 as [l [k [All D]]].
    eapply chain_to_end in H1 as H1'. 2: exact D. 2: auto. destruct H1'; subst.
    - destruct H0 as [n3 [n4 [l1 [l2 [k1 [k2 [eq _]]]]]]].
      congruence.
    - destruct H0 as [n3 D2].
      exists n3. split.
      + exists q, n3. split. 2: split. 1,3: apply internals_refl. auto.
      + eapply chain_to_front_iff in H1. 3: exact D2. 2: auto. exact H1.
        exists l, k. now split.
  * unfold onlyOne.
    exists q'. split. 2: apply internals_refl.
    exists q, q'. split. auto. split; auto. apply internals_refl.
Qed.

Goal forall ether, Node_equivalence (ether, 
                         0 : inl ([], ELet "X"%string (ELit 0%Z) (EVar 0), [], [], false) ||||
                         1 : inl ([], EConcBIF (ELit "send"%string) [EPid 0;ELit 1%Z], [], [], false) ||||
                         nullpool
                      )
                      (ether,
                        0 : inl ([], ELit 0%Z, [], [], false) ||||
                        1 : inl ([], EConcBIF (ELit "send"%string) [EPid 0;ELit 1%Z], [], [], false) ||||
                        nullpool
                      ).
Proof.
  exists internals. split.
  * apply internalSteps_weak_bisim.
  * exists [(AInternal, 0); (AInternal, 0)], 2. split.
    - repeat constructor.
    - eapply n_trans. do 3 constructor.
      eapply n_trans. do 4 constructor.
      simpl. apply n_refl.
Qed.

