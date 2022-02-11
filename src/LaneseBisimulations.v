Require Export ConcurrentFunSemantics.
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
      eapply nsend; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply narrive; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply nother; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply nspawn; try eassumption.
  }
  {
    subst. induction H0.
    * eexists. split. 2: reflexivity.
      eapply nsend; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply narrive; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply nother; try eassumption.
    * eexists. split. 2: reflexivity.
      eapply nspawn; try eassumption.
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








Definition internals (n n' : Node) : Prop :=
  exists l k, Forall (fun e => fst e = AInternal) l /\ n -[k|l]ₙ->* n'.

Notation "n -->* n'" := (internals n n') (at level 50).


(* Theorem extendStep : forall n n' ι,
  n -[ AInternal | ι ]ₙ-> n' -> forall r ι', ~In ι' (ppid n) -> ι' : r |||| n -[ AInternal | ι ]ₙ-> ι' : r |||| n'.
Proof.
  intros n n' ι H. inversion H; subst.
  intros. econstructor. 3: exact H2.
Admitted.

Theorem extendInternals :
  forall p q, p -->* q -> forall (r : Process) ι, ~In ι (ppid p) -> (ι : r |||| p) -->* (ι : r |||| q).
Proof.
   intros p q IND. induction IND; intros.
   * apply intrefl.
   * eapply inttrans. 2: apply IHIND; erewrite internalPids. 3: exact IND.
     2: { erewrite <- internalPids. 2: eapply inttrans; eauto. auto. }
     instantiate (1 := ι). apply extendStep; auto.
Qed. *)

Definition onlyOne (a : Action) (ι : PID) (n n''' : Node) :=
  exists n' n'', n -->* n' /\ n' -[a|ι]ₙ-> n'' /\ n'' -->* n'''.

Definition weak_bisimulation (R : Node -> Node -> Prop) :=
  (forall p q p' a ι, R p q -> p -[a | ι]ₙ-> p' ->
     exists q', onlyOne a ι q q' /\ R p' q') /\
  (forall p q q' a ι, R p q -> q -[a | ι]ₙ-> q' ->
     exists p', onlyOne a ι p p' /\ R p' q').

Definition Node_equivalence (n1 n2 : Node) := exists R, weak_bisimulation R /\ R n1 n2.

Lemma strong_bisim_is_weak : forall R, strong_bisimulation R -> weak_bisimulation R.
Proof.
  unfold strong_bisimulation, weak_bisimulation; intros. destruct H. split.
  * intros. eapply H in H2. 2: exact H1. destruct H2 as [q' [H2_1 H2_2]].
    exists q'. split; auto. exists q, q'. split. 2: split. 2: auto.
    all: exists [], 0; split; [constructor | constructor ]; auto.
  * intros. eapply H0 in H2. 2: exact H1. destruct H2 as [p' [H2_1 H2_2]].
    exists p'. split; auto. exists p, p'. split. 2: split. 2: auto.
    all: exists [], 0; split; [constructor | constructor ]; auto.
Qed.

(* Theorem processLocalDeterminism :
  forall p p' a ι, p -[ a | ι ]ₙ-> p' -> forall p'' a' ι', p -[ a' | ι' ]ₙ-> p'' -> p' = p'' /\ a = a' /\ ι = ι'.
Proof.
  intros p p' a ι IND. induction IND; intros.
Qed. *)

Lemma internal_determinism :
  forall p p' a, p -⌈a⌉-> p' -> forall p'', p -⌈a⌉-> p'' -> p' = p''.
Proof.
  intros p p' a IH. induction IH; intros.
  * inversion H0; subst; try (inversion H; inversion_is_value).
    2-3: inversion H; subst; try inversion_is_value.
    - eapply step_determinism in H. 2: exact H5. destruct H; now subst.
  * inversion H; subst; try inversion_is_value.
    - inversion H4; inversion_is_value.
    - auto.
  * inversion H0; subst; try inversion_is_value.
    - inversion H5; subst; inversion_is_value.
    - auto.
  * inversion H; subst; try inversion_is_value.
    - inversion H4; subst; inversion_is_value.
    - auto.
  * inversion H0; subst; try inversion_is_value.
    - inversion H5; subst; inversion_is_value.
    - auto.
  * inversion H1; subst; try inversion_is_value. auto.
  * inversion H0; now subst.
  * inversion H; now subst.
  * inversion H1; now subst.
  * inversion H1. subst. rewrite H in H7. now inversion H7.
Qed.

(* Lemma internal_alt : forall ether ether' procs procs' a ι p,
  (ether, procs) -[ a | ι ]ₙ-> (ether', procs') -> Some p = proc' ι -> Π -[ a | ι ]ₙ-> ι : p |||| Π'.
Proof.
  intros. generalize dependent p. induction H; intros; try rewrite par_same.
  * unfold par in H2; break_match_hyp. 2: congruence. inversion H2. subst. now apply nsend1.
  * unfold par in H1; break_match_hyp. 2: congruence. inversion H1. subst. eapply nsend2; eauto.
  * unfold par in H1; break_match_hyp. 2: congruence. inversion H1. subst. apply nsend3; eauto.
  * unfold par in H0; break_match_hyp. 2: congruence. inversion H0. subst. constructor; eauto.
  * unfold par in H0; break_match_hyp. 2: congruence. inversion H0. subst. constructor; eauto.
  * unfold par in H0; break_match_hyp. 2: congruence. inversion H0. subst. constructor; eauto.
  * unfold par in H2; break_match_hyp.
    - subst. unfold par in H0; break_match_hyp; congruence.
    - break_match_hyp. 2: congruence. inversion H2. subst. 
      rewrite par_swap, par_same. constructor; eauto. auto.
Qed. *)

Definition actionPid (a : Action) : option PID :=
match a with
 | ASend p t => Some p
 | AReceive t => None
 | AArrive t => None
 | ASelf ι => None
 | ASpawn ι t1 t2 => Some ι
 | AInternal => None
end.

Lemma par_eq : forall ι p p' Π Π',
  ι : p |||| Π = ι : p' |||| Π' -> p = p'.
Proof.
  intros. apply equal_f with ι in H as H'.
  unfold par in H'; break_match_hyp. 2: congruence. inversion H'. auto.
Qed.

(* Lemma concurrent_determinism :
  forall Π a ι Π', Π -[a | ι]ₙ-> Π' -> forall Π'', Π -[a | ι]ₙ-> Π'' -> Π' = Π''.
Proof.
  intros Π a ι Π' IH. induction IH; intros.
  * inversion H0; subst.
    - rewrite <- H3 in *.
      apply par_eq in H3 as H3'. subst.
      eapply internal_determinism in H. 2:exact H7. subst. auto. f_equal.
      extensionality ι''. apply equal_f with ι'' in H3. unfold par in *.
      break_match_goal; auto.
    - intuition; try congruence. destruct H4. congruence.
  * inversion H0; subst.
    apply par_eq in H3 as H3'. inversion H3'. subst.
    eapply internal_determinism in H. 2: exact H3. subst.
    extensionality ι''. apply equal_f with ι'' in H1. unfold par in *.
    break_match_goal; auto.
  * inversion H0; subst.
    apply par_eq in H1 as H1'. subst.
    eapply internal_determinism in H. 2: exact H2. subst.
    extensionality ι''. apply equal_f with ι'' in H1. unfold par in *.
    break_match_goal; auto.
  * inversion H0; subst.
    apply par_eq in H1 as H1'. subst.
    eapply internal_determinism in H. 2: exact H3. subst.
    extensionality ι''. apply equal_f with ι'' in H1. unfold par in *.
    break_match_goal; auto.
  * inversion H2; subst.
    apply par_eq in H3 as H3'. subst.
    eapply internal_determinism in H1. 2: exact H11. subst.
    extensionality ι''. apply equal_f with ι'' in H3. unfold par in *.
    break_match_goal; auto.
    rewrite H in H7. now inversion H7.
    break_match_goal; auto.
Qed. *)

(* Lemma action_swap : forall n n' n'' a ι a' ι',
  n -[a | ι]ₙ-> n' -> n -[a' | ι']ₙ-> n''
->
  n' -[a' | ι']ₙ-> n''. *)

(* Lemma none_action : forall n a ι p Π',
  n -[ a | ι ]ₙ-> ι : p |||| Π' ->
  actionPid a = None
->
  n -[a | ι]ₙ-> ι : p |||| n.
Proof.
  intros n a ι p Π' IH. dependent induction IH; subst; intro; simpl in *; try congruence.
  * apply par_eq in x as x'. subst. rewrite par_same. constructor; auto.
  * apply par_eq in x as x'. subst. rewrite par_same. constructor; auto.
  * apply par_eq in x as x'. subst. rewrite par_same. constructor; auto.
Qed. *)

(* Lemma internal_ordering_none_action :
  forall Π Θ, Π -->* Θ -> forall Π' a ι, Π -[a | ι]ₙ-> Π' ->
  forall p, Some p = Π' ι ->
  actionPid a = None
->
  Θ -[a | ι]ₙ-> ι : p |||| Θ.
Proof.
  intros Π Θ IH.
  destruct IH as [l [k [ALL IH]]]. dependent induction IH; intros.
  * eapply internal_alt in H0. 2: exact H. eapply concurrent_determinism in H. 2: exact H0.
    apply none_action in H0; auto.
  * inversion ALL; simpl in H5. subst.
    specialize (IHIH H6).
Qed. *)

Lemma internal_equal :
  forall p p', p -⌈ AInternal ⌉-> p' -> forall p'' a, p -⌈ a ⌉-> p''
->
  (a = AInternal /\ p'' = p') \/ (exists t, a = AArrive t /\ p'' = (fst (fst p), snd (fst p), snd p ++ [t])).
Proof.
  intros. inversion H; subst; inversion H0; subst.
  all: try (inversion H1; subst; inversion_is_value); auto; try inversion_is_value.
  * eapply step_determinism in H1. 2: exact H7. destruct H1. subst. auto.
  * right. exists v. auto.
  * inversion H6; inversion_is_value.
  * right. exists v. auto.
  * inversion H7; subst; inversion_is_value.
  * right. exists v0. auto.
  * inversion H6; subst; inversion_is_value.
  * right. exists v. auto. 
  * inversion H7; subst; inversion_is_value.
  * right. exists v0. auto.
Qed.

Definition modifyMailbox (p : PID) (ι0 : PID) (t : Exp) (n : Node) : Node :=
  let (g, procs) := n in (removeFirst (prod_eqdec Nat.eq_dec Exp_eq_dec) (ι0, t) g, 
                          fun ι => if Nat.eq_dec p ι
                                   then match procs ι with
                                         | Some (fs, e, mb) => Some (fs, e, mb ++ [t])
                                         | None => None
                                         end
                                    else procs ι).

Lemma internal_det :
  forall n n' n'' ι a, n -[AInternal | ι]ₙ-> n' -> n -[a | ι]ₙ-> n''
->
  (a = AInternal /\ n''= n') \/ (exists t, a = AArrive t /\ 
                                 n'' = modifyMailbox ι ι t n).
Proof.
  intros. inversion H. inversion H0; subst.
  * inversion H8; subst. apply par_eq in H5. subst.
    eapply internal_equal in H7; eauto. destruct H7 as [[? ?] | [? [? ?]]]; congruence.
  * right. inversion H9; subst. apply par_eq in H5; subst.
    eapply internal_equal in H8. 2: exact H1. destruct H8 as [[? ?] | [? [? ?]]]; try congruence.
    destruct p,p. simpl in H4. subst. exists t. simpl.
    split; auto. f_equal. extensionality ι'. unfold par.
    break_match_goal; auto. now inversion H3.
  * inversion H9; subst. apply par_eq in H5; subst.
    eapply internal_equal in H7. 2: exact H1. destruct H7 as [[? ?] | [? [? ?]]]; try congruence.
    - subst. left; split; auto. f_equal. inversion H9.
      extensionality x. apply equal_f with x in H4. unfold par in *. break_match_goal; auto.
    - subst. inversion H8. 2: inversion H3. 3: destruct H4. all: try congruence.
  * inversion H10; subst. apply par_eq in H5. subst.
    eapply internal_equal in H9; eauto. destruct H9 as [[? ?] | [? [? ?]]]; congruence.
Qed.

Lemma step_swap :
  forall n n' ι, n -[AInternal | ι]ₙ-> n' -> forall n'' a' ι', n -[a' | ι']ₙ-> n'' ->
  ι <> ι'
->
  exists n''', n' -[a' | ι']ₙ-> n'''.
Proof.
  intros n n' a ι IH. induction IH; intros.
  * inversion H0; subst.
    - exists (ether ++ [(ι', t)] ++ [(ι'1, t0)], ι'0 : p'0 |||| ι : p' |||| prs).
      destruct (Nat.eq_dec ι ι'0).
      + subst. apply par_eq in H4 as H4'. subst. eapply internal_determinism in H7. 2: exact H.
      eapply nsend.
Admitted.

Corollary alma :
  forall n n', n -->* n' -> forall n'' a ι, n -[a | ι]ₙ-> n''
->
  n' = n'' \/ exists n''', n' -[a | ι]ₙ-> n'''.
Proof.

Admitted. *)

Theorem internalSteps_weak_bisim : weak_bisimulation internals.
Proof.
  split; intros.
  * (* inversion H0; subst;  *) unfold onlyOne.
    eapply alma in H as H'. 2: exact H0. destruct H'; subst.
    - exists p'. split. 2: exists [], 0; repeat constructor.
      exists 
    - exists ((ether, ι : p'0 |||| ι' : q' |||| q)). split.
      + exists q. eexists. split. 2: split.
        ** exists [], 0; repeat constructor.
        ** admit.
        ** exists [], 0; repeat constructor.
      + 
Qed.

Goal Node_equivalence (
                         0 : ([], ELet "X"%string (ELit 0) (EVar 0), []) ||||
                         1 : ([], ESend (EPid 0) (ELit 1), []) ||||
                         nullnode
                      )
                      (
                        0 : ([], ELit 0, []) ||||
                        1 : ([], ELit 1, []) ||||
                        nullnode
                      ).
Proof.
  
Qed.