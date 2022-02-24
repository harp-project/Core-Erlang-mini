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








Definition internals (n n' : Node) : Prop :=
  exists l k, Forall (fun e => e.1 = AInternal) l /\ n -[k|l]ₙ->* n'.

Notation "n -->* n'" := (internals n n') (at level 50).

Theorem internals_refl :
  forall n, n -->* n.
Proof.
  intros. exists [], 0. split; auto. constructor.
Qed.

Theorem internals_trans :
  forall n n' n'', n -->* n' -> n' -->* n''
->
  n -->* n''.
Proof.
  intros. destruct H as [l1 [k1 [All1 D1]]]. destruct H0 as [l2 [k2 [All2 D2]]].
  exists (l1 ++ l2), (k1 + k2). split.
  * now apply Forall_app.
  * eapply closureNodeSem_trans; eassumption.
Qed.

Theorem bool_from_lit_val :
  forall y e, Some y = bool_from_lit e -> VALCLOSED e.
Proof.
  destruct e; intros; inversion H.
  now constructor.
Qed.

Definition onlyOne (a : Action) (ι : PID) (n n''' : Node) :=
  exists n' n'', n -->* n' /\ n' -[a|ι]ₙ-> n'' /\ n'' -->* n'''.

Lemma internal_determinism :
  forall p p' a, p -⌈a⌉-> p' -> forall p'', p -⌈a⌉-> p'' -> p' = p''.
Proof.
  intros p p' a IH. induction IH; intros.
  * inversion H0; subst; try (inversion H; inversion_is_value).
    - eapply step_determinism in H. 2: exact H7. destruct H. now subst.
  * inversion H1; subst; try inversion_is_value. auto.
  * inversion H0; now subst.
  * inversion H0; now subst.
  * inversion H0; now subst.
  * inversion H; now subst.
  * inversion H1; now subst.
  * inversion H1. subst. rewrite H in H9. now inversion H9.
  * inversion H0; subst.
    - rewrite <- H in H7. inversion H7. now subst.
  * inversion H0; subst.
    - reflexivity.
Qed.

Lemma par_eq : forall ι p p' Π Π',
  ι : p |||| Π = ι : p' |||| Π' -> p = p'.
Proof.
  intros. apply equal_f with ι in H as H'.
  unfold update in H'; break_match_hyp. 2: congruence. inversion H'. auto.
Qed.

Lemma concurrent_determinism :
  forall Π a ι Π', Π -[a | ι]ₙ-> Π' -> forall Π'', Π -[a | ι]ₙ-> Π'' -> Π' = Π''.
Proof.
  intros Π a ι Π' IH. inversion IH; intros; subst.
  * inversion H4; subst.
    - apply par_eq in H2 as H2'. subst.
      eapply internal_determinism in H. 2:exact H8. subst. auto. f_equal.
      extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence. destruct H0. congruence.
  * inversion H5; subst.
    - apply par_eq in H2 as H2'. inversion H2'. subst.
      eapply internal_determinism in H0. 2: exact H10. subst.
      f_equal. extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence. destruct H1. congruence.
  * inversion H5; subst.
    - intuition; try congruence. destruct H1. congruence.
    - intuition; try congruence. destruct H1. congruence.
    - apply par_eq in H2 as H2'. subst.
      eapply internal_determinism in H. 2: exact H3. subst. f_equal.
      extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence. destruct H1. congruence.
    - apply par_eq in H3 as H3'. subst.
      inversion H; subst; try inversion_is_value.
  * inversion H6; subst.
    - intuition; try congruence. destruct H2. congruence.
    - apply par_eq in H3 as H3'. subst.
      eapply internal_determinism in H1. 2: exact H12. subst.
      f_equal. rewrite H in H10. inversion H10. subst.
      extensionality ι''. apply equal_f with ι'' in H3. unfold update in *.
      break_match_goal; auto.
      break_match_goal; auto.
  * inversion H3; subst.
    - apply par_eq in H0 as H0'. subst.
      intuition; subst; try congruence. destruct H. congruence.
      inversion H1.
    - unfold update in *. f_equal.
      extensionality ι'. apply equal_f with ι' in H1. break_match_goal; auto.
Qed.

Lemma internal_equal :
  forall p p', inl p -⌈ AInternal ⌉-> p' -> forall p'' a, inl p -⌈ a ⌉-> p''
->
  (a = AInternal /\ p'' = p') \/
  (exists t ι ι', a = AArrive ι ι' t
   /\ exists p''', p' -⌈AArrive ι ι' t⌉-> p'''
  (*  /\ 
   match p'', t with
   | inl p'', Message t => p'' = (p.1.1.1.1, p.1.1.1.2, p.1.1.2 ++ [t], p.1.2, p.2)
   | inl p'', Exit t => 
   | inl p'', _ => False
   | inr dp, _  => False
   end *)).
Proof.
  intros. inversion H; subst; inversion H0; subst.
  all: try (inversion H2; subst; inversion_is_value); auto; try inversion_is_value.
  * eapply step_determinism in H2. 2: exact H9. destruct H2. subst. auto.
  * right. exists (Message v),source, dest. auto.
    split; auto. eexists. constructor; auto.
  * right. exists (Exit reason),source,dest.
    split; auto. eexists. constructor; auto.
  * apply bool_from_lit_val in H9. inversion H2; subst; inversion_is_value.
Qed.

Definition modifyMailbox (p : PID) (ι0 : PID) (ι : PID) (t : Exp) (n : Node) : Node :=
  let (g, procs) := n in (etherPop (ι0, ι, Message t) g, 
                      fun ι => if Nat.eq_dec p ι
                               then match procs ι with
                                     | Some (inl (fs, e, mb, links, flag)) =>
                                          Some (inl (fs, e, mb ++ [t], links, flag))
                                     | r => r
                                     end
                                else procs ι).

Theorem internal_is_alive :
  forall p p', p -⌈AInternal⌉-> p' -> exists pa, p = inl pa.
Proof.
  intros. inversion H; subst; try (do 2 eexists; split; reflexivity).
Qed.

Lemma internal_det :
  forall n n' n'' ι a, n -[AInternal | ι]ₙ-> n' -> n -[a | ι]ₙ-> n''
->
  (a = AInternal /\ n''= n') \/ (exists t ι', a = AArrive ι' ι t /\
                                 exists n''', n' -[AArrive ι' ι t | ι]ₙ-> n'''
  
                                (* /\
                                 n'' = modifyMailbox ι ι t n /\
                                 exists n''', n' -[AArrive t | ι]ₙ-> n''' /\
                                 n''' = modifyMailbox ι ι t n' *)).
Proof.
  intros. inversion H; inversion H0; subst.
  * inversion H8; subst. apply par_eq in H5. subst.
    apply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H7; eauto.
    destruct H7 as [[? ?] | [? [? [? [? ?]]]]];  congruence.
  * inversion H9; subst. apply par_eq in H5; subst.
    eapply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H8 as H8'. 2: exact H1.
    destruct H8' as [[? ?] | [? [? [? [? [? ?]]]]]]; try congruence.
    inversion H3. subst. right.
    do 2 eexists. split. reflexivity.
    eexists. econstructor; eauto.
  * inversion H9; subst. apply par_eq in H5; subst.
    apply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H7. 2: exact H1. destruct H7 as [[? ?] | [? [? [? [? [? ?]]]]]]; try congruence.
    - subst. left; split; auto. f_equal. inversion H9.
      extensionality x'. apply equal_f with x' in H4. unfold update in *. break_match_goal; auto.
    - subst. inversion H8. 2: destruct H3. 3: destruct H3.
      3-4: destruct H3. all: try congruence.
  * inversion H10; subst. apply par_eq in H5. subst.
    apply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H9; eauto. destruct H9 as [[? ?] | [? [? [? [? ?]]]]]; congruence.
  * inversion H7; subst. apply par_eq in H5. subst.
    inversion H1; subst; try inversion_is_value.
Qed.

Definition bothSpawn (a1 a2 : Action) : Prop:=
match a1, a2 with
| ASpawn _ _ _, ASpawn _ _ _ => True
| _, _ => False
end.

Lemma step_chain :
  forall n n' ι a, n -[a | ι]ₙ-> n' -> forall n'' a' ι' 
    (Spawns : ~ bothSpawn a a'), n -[a' | ι']ₙ-> n'' ->
  ι <> ι'
->
  exists n''', n' -[a' | ι']ₙ-> n'''.
Proof.
  intros n n' ι a IH. inversion IH; intros; subst.
  * inversion H4; subst.
    - exists ((ether ++ [(ι, ι', t)]) ++ [(ι'0, ι'1, t0)], ι'0 : p'0 |||| ι : p' |||| prs ).
      replace (ι : p' |||| prs) with (ι'0 : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality ι1. unfold update in *. apply equal_f with ι1 in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (etherPop (ι1, ι'0, t0) (ether ++ [(ι, ι', t)])
              , ι'0 : p'0 |||| ι : p' |||| prs ).
      replace (ι : p' |||| prs) with (ι'0 : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H1.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor. 2: auto.
      apply in_or_app. now left.
    - exists (ether ++ [(ι, ι', t)], ι'0 : p'0 |||| ι : p' |||| prs).
      replace (ι : p' |||| prs) with (ι'0 : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H1.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (ether ++ [(ι, ι', t)], 
              ι'1 : inl ([], EApp v1 l, [], [], false) |||| ι'0 : p'0 |||| ι : p' |||| prs).
      replace (ι : p' |||| prs) with (ι'0 : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H1.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
      apply equal_f with ι'1 in H1.
      unfold update in *. break_match_goal; auto.
      break_match_goal; subst.
      + congruence.
      + now rewrite H1 in H3.
    - exists (ether ++ [(ι, ι', t)],
               ι : p' |||| prs -- ι'0).
      replace (ι : p' |||| prs) with (ι'0 : inr [] |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      rewrite update_swap with (ι := ι); auto.
      constructor; auto.
  * inversion H5; subst.
    - exists (etherPop (ι1, ι, t) ether ++ [(ι', ι'0, t0)], ι' : p'0 |||| ι : p' |||| prs).
      replace (ι : p' |||| prs) with (ι' : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H3.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (etherPop (ι2, ι', t0) (etherPop (ι1, ι, t) ether)
              , ι' : p'0 |||| ι : p' |||| prs ).
      replace (ι : p' |||| prs) with (ι' : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor. 2: auto.
      apply removeFirst_In; auto. intro. apply H6. now inversion H1.
    - exists ((etherPop (ι1, ι, t) ether), ι' : p'0 |||| ι : p' |||| prs).
      replace (ι : p' |||| prs) with (ι' : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists ((etherPop (ι1, ι, t) ether), 
              ι'0 : inl ([], EApp v1 l, [], [], false) |||| ι' : p'0 |||| ι : p' |||| prs).
      replace (ι : p' |||| prs) with (ι' : p0 |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
      apply equal_f with ι'0 in H2.
      unfold update in *. break_match_goal; auto.
      break_match_goal; subst.
      + congruence.
      + now rewrite H2 in H4.
    - exists (etherPop (ι1, ι, t) ether,
               ι : p' |||| prs -- ι').
      replace (ι : p' |||| prs) with (ι' : inr [] |||| ι : p' |||| prs) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H3.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      rewrite update_swap with (ι := ι); auto.
      constructor; auto.
  * inversion H5; subst.
    - exists (ether ++ [(ι', ι'0, t)], ι' : p'0 |||| ι : p' |||| Π).
      replace (ι : p' |||| Π) with (ι' : p0 |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H3.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (etherPop (ι1, ι', t) ether
              , ι' : p'0 |||| ι : p' |||| Π ).
      replace (ι : p' |||| Π) with (ι' : p0 |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
    - exists (ether, ι' : p'0 |||| ι : p' |||| Π).
      replace (ι : p' |||| Π) with (ι' : p0 |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (ether, 
              ι'0 : inl ([], EApp v1 l, [], [], false) |||| ι' : p'0 |||| ι : p' |||| Π).
      replace (ι : p' |||| Π) with (ι' : p0 |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H2.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
      apply equal_f with ι'0 in H2.
      unfold update in *. break_match_goal; auto.
      break_match_goal; subst.
      + congruence.
      + now rewrite H2 in H4.
    - exists (ether,
               ι : p' |||| Π -- ι').
      replace (ι : p' |||| Π) with (ι' : inr [] |||| ι : p' |||| Π) at 1.
      2: { extensionality ι1. unfold update in *. apply equal_f with ι1 in H3.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      rewrite update_swap with (ι := ι); auto.
      constructor; auto.
  * inversion H6; subst.
    - exists (ether ++ [(ι'0, ι'1, t)], ι'0 : p'0 |||| 
                                        ι' : inl ([], EApp v1 l, [], [], false) |||| 
                                        ι : p' |||| Π).
      replace (ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) with 
              (ι'0 : p0 |||| ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H4.
           break_match_goal; subst;
           break_match_goal; subst; auto.
           all: break_match_hyp; auto; congruence.
         }
      now constructor.
    - exists (etherPop (ι1, ι'0, t) ether
              , ι'0 : p'0 |||| ι' : inl ([], EApp v1 l, [], [], false) 
                          |||| ι : p' |||| Π ).
      replace (ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) with 
              (ι'0 : p0 |||| ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H3.
           break_match_goal; subst;
           break_match_goal; subst; auto.
           all: break_match_hyp; auto; try congruence.
         }
      constructor; auto.
    - exists (ether, ι'0 : p'0 |||| ι' : inl ([], EApp v1 l, [], [], false)
                               |||| ι : p' |||| Π).
      replace (ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) with 
              (ι'0 : p0 |||| ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H3.
           break_match_goal; subst;
           break_match_goal; subst; auto.
           all: break_match_hyp; auto; congruence.
         }
      now constructor.
    - (** cannot be sure to generate different spawn PID-s *)
      exfalso. apply Spawns. cbn. auto.
    - exists (ether,
               ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π -- ι'0).
      replace (ι' : inl ([], EApp v1 l, [], [], false) |||| ι : p' |||| Π) with 
              (ι'0 : inr [] |||| ι' : inl ([], EApp v1 l, [], [], false) 
                            |||| ι : p' |||| Π) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H4.
           break_match_goal; subst.
           break_match_goal; subst. congruence.
           break_match_goal; auto. congruence.
           break_match_goal; auto.
         }
      rewrite update_swap with (ι := ι); auto.
      rewrite update_swap with (ι := ι') (ι' := ι'0); auto.
      constructor; auto.
      apply equal_f with ι' in H4. unfold update in H4. cbn in H4.
      break_match_hyp; auto; subst. break_match_hyp; subst; try congruence; auto.
      unfold update in H0. break_match_hyp; congruence.
  * inversion H3; subst.
    - exists (ether ++ [(ι', ι'0, t)], ι' : p' |||| (Π -- ι)).
      replace (Π -- ι) with (ι' : p |||| (Π -- ι)) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H1.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (etherPop (ι1, ι', t) ether
              , ι' : p' |||| (Π -- ι) ).
      replace (Π -- ι) with (ι' : p |||| (Π -- ι)) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H0.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
    - exists (ether, ι' : p' |||| (Π -- ι)).
      replace (Π -- ι) with (ι' : p |||| (Π -- ι)) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H0.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      now constructor.
    - exists (ether, 
              ι'0 : inl ([], EApp v1 l, [], [], false) |||| ι' : p' |||| (Π -- ι)).
      replace (Π -- ι) with (ι' : p |||| (Π -- ι)) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H0.
           break_match_goal; subst.
           break_match_goal; subst. congruence. auto.
           auto.
         }
      constructor; auto.
      apply equal_f with ι'0 in H0.
      unfold update in *. break_match_goal; auto.
      break_match_goal; subst; auto. congruence.
    - exists (ether, (Π -- ι) -- ι').
      replace (Π -- ι) with (ι' : inr [] |||| (Π -- ι)) at 1.
      2: { extensionality x. unfold update in *. apply equal_f with x in H1.
           break_match_goal; subst. auto.
           break_match_goal; subst. congruence. auto.
           break_match_goal; subst; auto.
         }
      constructor; auto.
Qed.

Corollary chain_to_end :
  forall n n' l k, n -[k | l]ₙ->* n' -> Forall (fun a => a.1 = AInternal) l -> 
   forall n'' a ι, n -[a | ι]ₙ-> n''
->
  (exists n3 n4 l1 l2 k1 k2, a = AInternal /\ 
    n -[k1 | l1]ₙ->* n3 /\ n3 -[a |ι]ₙ-> n4 /\ n4 -[k2 | l2]ₙ->* n' /\
    k = S k1 + k2 /\ l = l1 ++ [(a, ι)] ++ l2
  ) \/ 
  (exists n''', n' -[a | ι]ₙ-> n''').
Proof.
  intros n n' l k Steps.
  dependent induction Steps; intros.
  * right. eexists. eauto.
  * inversion H0; subst. simpl in H4. subst.
    destruct (Nat.eq_dec ι ι0); subst.
    - eapply internal_det in H1 as H1'. 2: exact H.
      destruct H1' as [[eq1 eq2] | [t H0']]; subst.
      + left. exists n, n', [], l, 0, k. split; auto.
        split. 2: split. constructor.
        auto.
        split; auto.
      + destruct H0' as [source [eq [n''' D]]]. subst.
        inversion H1; subst.
        2: { intuition; try congruence. destruct H4; congruence. }
        inversion H10; subst.
        ** specialize (IHSteps H5 _ _ _ D).
           destruct IHSteps as [[n3 [n4 [l1 [l2 [k1 [k2 H2]]]]]]| [n3 D2]].
           -- left. destruct H2 as [eq1 [D1 [D2 [ D3 [eq2 eq3]]]]]. subst.
              congruence.
           -- right. eexists; eauto.
        ** specialize (IHSteps H5 _ _ _ D).
           destruct IHSteps as [[n3 [n4 [l1 [l2 [k1 [k2 H2]]]]]]| [n3 D2]].
           -- left. destruct H2 as [eq1 [D1 [D2 [ D3 [eq2 eq3]]]]]. subst.
              congruence.
           -- right. eexists; eauto.
    - eapply step_chain in H1. 2: exact H. 2-3: auto.
      destruct H1. eapply IHSteps in H1 as H1'; auto.
      destruct H1' as [[n3 [n4 [l1 [l2 [k1 H2]]]]] | [t H0']]; subst.
      + left. destruct H2 as [k2 [eq1 [D1 [D2 [ D3 [eq2 eq3]]]]]]. subst.
        exists n3, n4, ((AInternal, ι)::l1), l2, (S k1), k2. split; auto.
        split. 2: split. 3: split. all: auto.
        eapply n_trans. 2: exact D1. auto.
      + right. now exists t.
Qed.

Lemma internal_keep :
  forall n n' ι, n -[AInternal | ι]ₙ-> n'
->
  forall x, x <> ι -> snd n x = snd n' x.
Proof.
  intros. inversion H; subst.
  simpl. unfold update. break_match_goal; auto. congruence.
Qed.

(* general case wont work: message ordering is desructed *)
Theorem diamond_derivations :
  forall n1 n2 n3 n4 a ι1 ι2, ι1 <> ι2 ->
  n1 -[AInternal | ι1]ₙ-> n2 -> n1 -[a | ι2]ₙ-> n3 -> n2 -[a | ι2]ₙ-> n4
->
  n3 -[AInternal | ι1]ₙ-> n4.
Proof.
  intros.
  inversion H2; subst.
  * inversion H1; subst.
    inversion H0; subst.
    2: { intuition; try congruence. destruct H6; congruence. }
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H3. 2: exact H10. subst.
    assert ((ι1 : p1 |||| ι2 : p' |||| prs0) = ι1 : p1 |||| ι2 : p' |||| prs) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto. auto.
    }
    replace (ι2 : p' |||| prs0) with (ι1 : p1 |||| ι2 : p' |||| prs0).
    replace (ι2 : p' |||| prs) with (ι1 : p'1 |||| ι2 : p' |||| prs).
    rewrite EQ. constructor; auto.
    all: unfold update in *; extensionality x; 
         apply equal_f with x in H5; apply equal_f with x in H12;
         do 2 break_match_goal; subst; auto; congruence.
  * inversion H1; subst.
    inversion H0; subst.
    2: { intuition; try congruence. destruct H7; congruence. }
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H4. 2: exact H12. subst.
    assert ((ι1 : p1 |||| ι2 : p' |||| prs0) = ι1 : p1 |||| ι2 : p' |||| prs) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto. auto.
    }
    replace (ι2 : p' |||| prs0) with (ι1 : p1 |||| ι2 : p' |||| prs0).
    replace (ι2 : p' |||| prs) with (ι1 : p'1 |||| ι2 : p' |||| prs).
    rewrite EQ. constructor; auto.
    all: unfold update in *; extensionality x; 
         apply equal_f with x in H6; apply equal_f with x in H14;
         do 2 break_match_goal; subst; auto; congruence.
  * inversion H1; subst.
    1,2,4,5: intuition; try congruence;
      match goal with
      | [H : exists _, _ |- _] => destruct H; congruence
      | _ => idtac
      end.
    - inversion H0; subst.
      assert (p = inr []). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. congruence.
        auto.
      }
      subst.
      inversion H3.
    - inversion H0; subst.
      assert (p = p0). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. congruence.
        auto.
      }
      subst.
      subst. eapply internal_determinism in H3. 2: exact H5. subst.
      assert ((ι1 : p1 |||| ι2 : p' |||| Π0) = ι1 : p1 |||| ι2 : p' |||| Π) as EQ. {
        extensionality x. unfold update in *. break_match_goal; auto.
        apply internal_keep with (x := x) in H0. simpl in H0.
        break_match_goal; auto. auto.
      }
      replace (ι2 : p' |||| Π0) with (ι1 : p1 |||| ι2 : p' |||| Π0).
      replace (ι2 : p' |||| Π) with (ι1 : p'1 |||| ι2 : p' |||| Π).
      rewrite EQ. constructor; auto.
      1-2: unfold update in *; extensionality x; 
           apply equal_f with x in H8; apply equal_f with x in H13;
           do 2 break_match_goal; subst; auto; congruence.
  * inversion H1; subst.
    1: intuition; try congruence; destruct H8; congruence.
    inversion H0; subst.
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H5. 2: exact H14. subst.
    assert ((ι1 : p1 |||| ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π0) = 
             ι1 : p1 |||| ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto.
      auto.
    }
    rewrite H3 in H10. inversion H10. subst.
    replace (ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π0) with
            (ι1 : p1 |||| ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π0).
    replace (ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π) with
            (ι1 : p'1 |||| ι' : inl ([], EApp v1 l0, [], [], false) |||| ι2 : p' |||| Π).
    rewrite EQ. apply n_other; auto.
    clear EQ H1 H2 H0.
    all: unfold update in *; extensionality x;
         apply equal_f with x in H7; apply equal_f with x in H15;
         do 2 break_match_goal; subst; auto; try congruence.
    - break_match_goal; auto. subst. congruence.
    - break_match_goal; auto. subst. congruence.
  * inversion H1; subst.
    1: intuition; try congruence. destruct H5; congruence.
    - inversion H0; subst.
      assert (p = inr []). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. congruence.
        auto.
      }
      subst.
      inversion H3.
    - inversion H0. subst.
      assert ((ι1 : p |||| (Π0 -- ι2)) = 
               ι1 : p |||| (Π  -- ι2)) as EQ. {
        extensionality x. unfold update in *. break_match_goal; auto.
        apply internal_keep with (x := x) in H0. simpl in H0.
        break_match_goal; auto. auto.
      }
      replace (Π0 -- ι2) with
              (ι1 : p |||| (Π0 -- ι2)).
      replace (Π -- ι2) with
              (ι1 : p' |||| (Π -- ι2)).
      rewrite EQ. constructor; auto.
      all: unfold update in *; extensionality x;
       apply equal_f with x in H4; apply equal_f with x in H9;
       do 2 break_match_goal; subst; auto; try congruence.
Qed.

Theorem delay_internal_same :
  forall n n1 ι,   n -[AInternal | ι]ₙ-> n1 ->
  forall n2 a, n1 -[a | ι]ₙ-> n2 ->
       forall n3, n -[a | ι]ₙ-> n3
->
  n3 -[AInternal | ι]ₙ-> n2.
Proof.
  intros. inversion H; subst.
  eapply internal_det in H1 as H1'. 2: exact H.
  destruct H1' as [[eq1 eq2]| [t [? [eq [n'' D]]]]]; subst.
  * auto.
  * inversion H0; subst.
    2: { intuition; try congruence; destruct H3; congruence. }
    simpl. apply par_eq in H5 as H5'. subst.
    inversion H1; subst.
    - simpl. apply par_eq in H6 as H5'. subst.
      apply n_other. 2: now left.
      inversion H10; subst.
      inversion H2; simpl; subst.
      - constructor; auto.
Qed.

Corollary chain_to_front_iff :
  forall n n', n -->* n' -> forall a ι n'' n3, (* a <> AInternal -> *)
  n' -[a | ι]ₙ-> n'' ->
  n  -[a | ι]ₙ-> n3
->
  n3 -->* n''.
Proof.
  intros n n' D.
  destruct D as [l [k [All D]]]. induction D; intros.
  * eapply concurrent_determinism in H. 2: exact H0. subst. apply internals_refl.
  * inversion All; simpl in H4. subst.
    destruct (Nat.eq_dec ι0 ι).
    - subst.
      eapply internal_det in H1 as H2'. 2: exact H.
      destruct H2' as [[? ?] | [t [? [? [n4 [D1 ?]]]]]]; subst.
      + eapply internals_trans.
        exists l, k. split; eauto.
        exists [(AInternal, ι)], 1. split. repeat constructor.
        eapply n_trans; eauto. constructor.
      + epose proof (delay_internal_same _ _ _ H _ _ D1 _ H1).
        epose proof (IHD H5 _ _ _ _ H0 D1).
        eapply internals_trans. 2: exact H3.
        exists [(AInternal, ι)], 1. split. repeat constructor.
        eapply n_trans. exact H2. apply n_refl.
    - apply not_eq_sym in n0.
      epose proof (D2 := step_chain _ _ _ _ H _ _ _ _ H1 n0).
      destruct D2 as [n4 D2].
      epose proof (IHD H5 _ _ _ _ H0 D2).

      eapply internals_trans. 2: exact H2.
      exists [(AInternal, ι)], 1. split. repeat constructor.
      eapply n_trans. 2: apply n_refl.
      clear IHD H5 D All H2 H0.
      now epose proof (diamond_derivations _ _ _ _ _ _ _ n0 H H1 D2).
  Unshelve.
  ** intro. destruct a0; auto.
Qed.

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
      + 
        eapply chain_to_front_iff in H1. 3: exact D2. 2: auto. exact H1.
        exists l, k. now split.
  * unfold onlyOne.
    exists q'. split. 2: apply internals_refl.
    exists q, q'. split. auto. split; auto. apply internals_refl.
Qed.

Goal Node_equivalence ([], 
                         0 : inl ([], ELet "X"%string (ELit 0%Z) (EVar 0), [], [], false) ||||
                         1 : inl ([], EConcBIF (ELit "send"%string) [EPid 0;ELit 1%Z], [], [], false) ||||
                         nullpool
                      )
                      ([],
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