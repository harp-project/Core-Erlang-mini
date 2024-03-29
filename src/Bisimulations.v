(**
  This file is a part of a formalisation of a subset of Core Erlang.

  In this file, we show bisimulation-based equivalence concepts for
  concurrent Core Erlang.
*)

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
    subst. eexists. split. exact H0. auto.
  }
  {
    subst. eexists. split. exact H0. auto.
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
    all: exists []; split; [constructor | constructor ]; auto.
  * intros. eapply H0 in H3. 2: exact H2. destruct H3 as [p' [H3_1 H3_2]].
    exists p'. split; auto. exists p, p'. split. 2: split. 2: auto.
    all: exists []; split; [constructor | constructor ]; auto.
Qed.

Theorem internalSteps_weak_bisim : weak_bisimulation internals.
Proof.
 split; intros.
  * unfold onlyOne.
    destruct H0 as [l [All D]].
    eapply chain_to_end in H1 as H1'. 2: exact D. 2: auto. destruct H1'; subst.
    - destruct H0 as [n3 [n4 [l1 [l2 [eq _]]]]].
      congruence.
    - destruct H0 as [n3 D2].
      exists n3. split.
      + exists q, n3. split. 2: split. 1,3: apply internals_refl. auto.
      + eapply chain_to_front_iff in H1. 3: exact D2. 2: auto. exact H1.
        exists l. now split.
  * unfold onlyOne.
    exists q'. split. 2: apply internals_refl.
    exists q, q'. split. auto. split; auto. apply internals_refl.
Qed.

Goal forall ether, Node_equivalence (ether, 
                         0 : inl ([], ELet "X"%string (ELit 0%Z) (EVar 0), [], [], false) ||||
                         1 : inl ([], EBIF (ELit "!"%string) [EPid 0;ELit 1%Z], [], [], false) ||||
                         nullpool
                      )
                      (ether,
                        0 : inl ([], ELit 0%Z, [], [], false) ||||
                        1 : inl ([], EBIF (ELit "!"%string) [EPid 0;ELit 1%Z], [], [], false) ||||
                        nullpool
                      ).
Proof.
  exists internals. split.
  * apply internalSteps_weak_bisim.
  * exists [(AInternal, 0); (AInternal, 0)]. split.
    - repeat constructor.
    - eapply n_trans. do 3 constructor.
      eapply n_trans. do 4 constructor.
      simpl. apply n_refl.
Qed.

Fixpoint list_app (e1 e2 : Exp) : Exp :=
  match e1 with
  | ENil => e2
  | ECons e1' e2' => ECons e1' (list_app e2' e2)
  | _ => ENil
  end.

Theorem internals_to_locals Fs Fs' e e' k mb links flag:
  ⟨Fs, e⟩ -[k]-> ⟨Fs', e'⟩ ->
  inl (Fs, e, mb, links, flag) -⌈repeat AInternal k⌉->*
  inl (Fs', e', mb, links, flag).
Proof.
  intros. induction H; simpl in *; econstructor.
  - constructor. eassumption.
  - eassumption.
Qed.



Theorem locals_to_inter_nodes p p' Δ Π l l' pid:
  Forall (fun a => a = AInternal) l ->
  l' = map (fun a => (a, pid)) l ->
  p -⌈l⌉->* p' ->
  (Δ, pid : p |||| Π) -[l']ₙ->* (Δ, pid : p' |||| Π).
Proof.
  intros. subst. induction H1; econstructor.
  - constructor. eassumption. inversion H; subst. now left.
  - apply IHLabelStar. now inversion H.
Qed.

Goal forall Δ Π e x f (l : Exp) l' pid Fs,
  cons_to_list l = Some l' ->
  VALCLOSED l ->
  EXP 2 ⊢ e ->
  computes x e f ->
  Node_equivalence
  (Δ, pid : inl (Fs, obj_map (EFun [x] e) l, [], [], false) |||| Π)
  (Δ, pid : inl (Fs, list_to_cons (map f l'), [], [], false) |||| Π).
Proof.
  exists internals. split.
  * apply internalSteps_weak_bisim.
  * eapply obj_map_on_meta_level in H. 4: eassumption. all: auto.
    destruct H as [Hcl [k D]].
    exists (repeat (AInternal, pid) k). split.
    - clear. induction k; constructor; auto.
    - eapply locals_to_inter_nodes with (l := repeat AInternal k).
      2: {
        clear.
        induction k; simpl.
        reflexivity. now rewrite IHk.
      }
      {
        clear. induction k; now constructor.
      }
      apply internals_to_locals.
      eapply frame_indep_nil in D. exact D.
Qed.

Lemma update_get :
  forall T x (a : T) f, update x a f x = a.
Proof.
  intros. unfold update. now rewrite Nat.eqb_refl.
Qed.

Lemma any_step_is_not_bisimilar: exists l,
  ~weak_bisimulation (fun Π Σ => Π -[ l ]ₙ->* Σ).
Proof.
  exists [(AInternal, 0); (AInternal, 0)]. intro. destruct H. clear H0.
  remember (etherAdd 1 0 (Exit (ELit "kill"%string) false) (fun (_ _ : PID) => @nil Signal), 0 : inl ([], ELet "X"%string (ELit 0%Z) (EVar 0), [], [], false) |||| nullpool) as Π.
  remember (etherAdd 1 0 (Exit (ELit "kill"%string) false) (fun (_ _ : PID) => @nil Signal), 0 : inl ([], ELit 0%Z, [], [], false) |||| nullpool) as Σ.
  remember (fun (_ _ : PID) => @nil Signal, 0 : inr [] |||| nullpool) as Π'.
  assert (Π -[ [(AInternal, 0); (AInternal, 0)] ]ₙ->* Σ) as D1. {
    subst. econstructor.
    constructor; auto. do 2 constructor.
    econstructor. constructor; auto. do 3 constructor.
    constructor.
  }
  assert (Π -[ AArrive 1 0 (Exit (ELit "kill"%string) false) | 0 ]ₙ-> Π') as D2. {
    subst. constructor. cbn. unfold etherAdd, update. cbn.
    do 2 f_equal. extensionality x. destruct x; auto.
    destruct x; auto.
    extensionality x. destruct x; auto.
    replace [] with (map (fun x:PID => (x, killed)) []) by auto.
    apply p_exit_terminate; auto.
  }
  specialize (H Π Σ Π' (AArrive 1 0 (Exit (ELit "kill"%string) false)) 0 ltac:(congruence) D1 D2).
  destruct H as [Σ' [H_1 H_2]].
  subst. clear D2 D1.
  inversion H_2; subst.
  inversion H4; subst. clear H7.
  apply equal_f with 0 in H0. inversion H0; subst.
  inversion H1.
Qed.

