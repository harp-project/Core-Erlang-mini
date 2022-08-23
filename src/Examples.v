Require Import ConcurrentFunSemantics.
Import ListNotations.
Import PeanoNat.
(*
  0 -[ 1 + 1 ]-> 1
  1 -[ 2 ]-> 3
  2 -[ 3 ]-> 3
  3 : 2 + 3 == 5
*)
Open Scope string_scope. Print LiveProcess.

Ltac ether_order_base X :=
  match X with
  | context G [@update ?ty ?i1 ?inner (@update _ ?i2 _ ?ether)] =>
    match ty with
    | PID -> list Signal =>
      match eval compute in (Nat.leb i1 i2) with
      | true  => idtac inner; ether_order_base inner; ether_order_base ether
      | false => rewrite (update_swap _ i1 i2 _ _ ether)
      end
    | list Signal =>
      match eval compute in (Nat.leb i1 i2) with
      | true  => idtac inner; ether_order_base ether
      | false => rewrite (update_swap _ i1 i2 _ _ ether)
      end
    end
  end.
Ltac ether_order :=
  match goal with
  | |- (?X, _) -[ _ | _ ]ₙ->* (_, _) => ether_order_base X
  end.

Corollary update_noop_ether_1 :
  forall A ι2, update ι2 (@nil A) (fun _ => []) = fun _ => [].
Proof.
  intros. rewrite update_noop; reflexivity.
Qed.

Corollary update_noop_ether_2 :
  forall {T} ι1, @update (PID -> list T) ι1 (fun _ => []) (fun _ _ => []) = fun _ _ => [].
Proof.
  intros. rewrite update_noop; reflexivity.
Qed.

Ltac ether_cleanup :=
  unfold nullpool, etherAdd; cbn;
  try ether_order; try lia;
  repeat rewrite update_same;
  repeat rewrite update_noop_ether_1;
  repeat rewrite update_noop_ether_2.

(** Signal ordering tests: *)
Example signal_ordering :
  exists acts k,
    (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF (ELit "send") [EPid 1; ELit "fst"])
                                        (EConcBIF (ELit "send") [EPid 2; ELit "snd"]), [], [], false) ||||
                  1 : inl ([], EReceive [(PVar, EConcBIF (ELit "send")
                                                       [EPid 2; EVar 0])], [], [], false) ||||
                  2 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
    (fun _ _ => [], 2 : inl ([], ELit "snd", [ELit "fst"], [], false) |||| nullpool).
Proof.
  eexists. exists 23.
  (* Progress with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    constructor. apply step_concbif. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  simpl. ether_cleanup.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 0).
  ether_cleanup.
  rewrite par_swap with (ι := 1) (ι' := 2).
  rewrite par_swap with (ι := 0) (ι' := 2).
  rewrite par_swap with (ι := 0) (ι' := 1).
  rewrite nullpool_remove. 2-4: lia.
  rewrite par_swap. 2: lia.
  (* Messages are delivered: *)
  eapply n_trans. eapply n_arrive with (ι := 1) (ι0 := 0).
    reflexivity. do 2 constructor. simpl.
  ether_cleanup.
  rewrite par_swap. 2: lia.
  eapply n_trans. eapply n_arrive with (ι := 2) (ι0 := 0).
    reflexivity. do 2 constructor. simpl.
  ether_cleanup.
  (* Progress with 2 *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
  rewrite par_swap with (ι := 2) (ι' := 1). 2: lia.
  ether_cleanup.
  (* Progress with 1 *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
    ether_cleanup.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 1).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 1).
    rewrite par_swap. 2: lia. rewrite nullpool_remove.
  (* Arrive to 2 *)
  eapply n_trans. eapply n_arrive with (ι := 2) (ι0 := 1).
    reflexivity. do 2 constructor. simpl.
    ether_cleanup.
  apply n_refl.
Qed.

Example signal_ordering_2 :
  exists acts k,
    (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF (ELit "send") [EPid 1; ELit "fst"])
                                        (EConcBIF (ELit "send") [EPid 2; ELit "snd"]), [], [], false) ||||
                  1 : inl ([], EReceive [(PVar, EConcBIF (ELit "send")
                                                       [EPid 2; EVar 0])], [], [], false) ||||
                  2 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
    (fun _ _ => [], 2 : inl ([], ELit "snd", [ELit "fst"], [], false) |||| nullpool).
Proof.
  eexists. exists 23.
  (* Progress with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    constructor. apply step_concbif. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 0).
  ether_cleanup.
  rewrite par_swap with (ι := 1) (ι' := 2).
  rewrite par_swap with (ι := 0) (ι' := 2).
  rewrite par_swap with (ι := 0) (ι' := 1).
  rewrite nullpool_remove. 2-4: lia.
  rewrite par_swap. 2: lia.
  (* Messages are delivered: *)
  eapply n_trans. eapply n_arrive with (ι := 1) (ι0 := 0).
    reflexivity. do 2 constructor. simpl.
  ether_cleanup.
  rewrite par_swap. 2: lia.
  eapply n_trans. eapply n_arrive with (ι := 2) (ι0 := 0).
    reflexivity. do 2 constructor. simpl.
  ether_cleanup.
  rewrite par_swap. 2: lia.
  (* Progress with 1 *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
    ether_cleanup.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 1).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 1).
    rewrite par_swap. 2: lia. rewrite nullpool_remove.
  (* Progress with 2 *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
  eapply n_trans. eapply n_arrive with (ι := 2) (ι0 := 1).
    reflexivity. do 2 constructor. simpl.
    ether_cleanup.
  apply n_refl.
Qed.

Example signal_ordering_3 :
  exists acts k,
    (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF (ELit "send") [EPid 1; ELit "fst"])
                                        (EConcBIF (ELit "send") [EPid 2; ELit "snd"]), [], [], false) ||||
                  1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) ||||
                  2 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
    (etherAdd 0 2 (Message (ELit "snd")) (fun _ _ => []),
                  1 : inl ([], ELit "fst", [], [], false) ||||
                  2 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool).
Proof.
  eexists. exists 14.
  (* Progress with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    constructor. apply step_concbif. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 0).
  ether_cleanup.
  rewrite par_swap with (ι := 0) (ι' := 1).
  rewrite par_swap with (ι := 0) (ι' := 2).
  rewrite nullpool_remove. 2-3: lia.
  (* Messages are delivered *)
  eapply n_trans. eapply n_arrive with (ι := 1) (ι0 := 0).
    reflexivity. do 2 constructor. simpl.
  ether_cleanup.
  (* Now 1 can progress *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
  rewrite update_noop with (x := 1) by reflexivity.
  apply n_refl.
Qed.

Example signal_ordering_4 :
  exists acts k,
    (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF (ELit "send") [EPid 1; ELit "fst"])
                                        (EConcBIF (ELit "send") [EPid 2; ELit "snd"]), [], [], false) ||||
                  1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) ||||
                  2 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
    (etherAdd 0 1 (Message (ELit "fst")) (fun _ _ => []),
                  1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) ||||
                  2 : inl ([], ELit "snd", [], [], false) |||| nullpool).
Proof.
  eexists. exists 14.
  (* Progress with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    constructor. apply step_concbif. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor.
  ether_cleanup. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate with (ι := 0).
  ether_cleanup.
  rewrite par_swap with (ι := 0) (ι' := 1).
  rewrite par_swap with (ι := 0) (ι' := 2).
  rewrite nullpool_remove. 2-3: lia.
  rewrite par_swap with (ι := 1) (ι' := 2). 2: lia.
  (* Messages are delivered *)
  eapply n_trans. eapply n_arrive with (ι := 2) (ι0 := 0).
    reflexivity. do 2 constructor.
  ether_cleanup.
  (* Now 2 can progress too *)
  eapply n_trans. eapply n_other.
    apply p_receive; auto. simpl. reflexivity. do 2 right. left. now eexists. cbn.
    break_match_goal. 2: congruence.
  rewrite par_swap with (ι := 1) (ι' := 2). 2: lia.
  apply n_refl.
Qed.

(** Further tests: *)

Goal exists acts k,
  (fun _ _ => [], 0 : inl ([], EConcBIF (ELit "send") [EPid 1;EPlus (ELit 1%Z) (ELit 1%Z)], [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EConcBIF (ELit "send") [EPid 3;EVar 0])], [], [], false) ||||
       2 : inl ([], EConcBIF (ELit "send") [EPid 3;ELit 3%Z], [], [], false) ||||
       3 : inl ([], EReceive [(PVar, EReceive [(PVar, EPlus (EVar 0) (EVar 1))])], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
  (fun _ _ => [], 0 : inl ([], ELit 2%Z, [], [], false) ||||
       1 : inl ([], ELit 2%Z, [], [], false) ||||
       2 : inl ([], ELit 3%Z, [], [], false) ||||
       3 : inl ([], ELit 5%Z, [], [], false) |||| nullpool).
Proof.
  eexists. exists 24.
  (* Some steps with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 4 constructor. auto.
  simpl. eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  simpl.

  rewrite par_swap with (ι' := 2). rewrite par_swap with (ι' := 2). 2-3: lia.

  (* Some steps with 2 *)
  eapply n_trans. eapply n_other with (ι := 2).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 2).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 2).
    do 3 constructor. auto.
  simpl.

  rewrite par_swap with (ι' := 3). rewrite par_swap with (ι' := 3). 2-3: lia.

  eapply n_trans. eapply n_send with (ι := 2) (ι' := 3).
    constructor. constructor.
  simpl.

  rewrite par_swap with (ι' := 3). 2: lia.
  eapply n_trans. apply n_arrive with (ι0 := 2).
    reflexivity. repeat constructor.
  cbn.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0). 2-3: lia.

  (* Again with 0 *)

  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 1). 2-3: lia.

  eapply n_trans. eapply n_send with (ι := 0) (ι' := 1).
  constructor. constructor. simpl.

  rewrite par_swap with (ι' := 1). 2: lia.
  eapply n_trans. apply n_arrive with (ι0 := 0).
    reflexivity. repeat constructor.
  cbn.

  (* Now with 1 *)
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_receive; try reflexivity. right. right. left. eexists. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.

  cbn. break_match_goal. 2: congruence.
  rewrite par_swap with (ι' := 3). 2: lia.

  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 1) (ι' := 3).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 3). 2: lia.

  eapply n_trans. apply n_arrive with (ι0 := 1).
    reflexivity. repeat constructor.
  cbn.

  (* Mailbox processing for 3 *)
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_receive; try reflexivity. right. right. left. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_receive; try reflexivity. right. right. left. eexists. auto.
    cbn. break_match_goal. 2: congruence.

  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. auto.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0).
  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 2).

  repeat ether_cleanup.
  apply n_refl.
  all: lia.
Qed.


#[export]
Hint Constructors ValScoped : core.
#[export]
Hint Constructors ExpScoped : core.
(*

let X = spawn(fun() -> receive X -> X ! self() end end, [])
  in let Y = X ! self()
    in receive X -> X end

*)
Goal exists acts k,
  (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF (ELit "spawn") [EFun [] (EReceive [(PVar, EConcBIF (ELit "send") [EVar 0; EConcBIF (ELit "self") []])]);
                                             ENil])
             (ELet "Y"%string (EConcBIF (ELit "send") [EVar 0; EConcBIF (ELit "self") []])
                 (EReceive [(PVar, EVar 0)]))
                  , [], [], false)
  |||| nullpool)
  -[ k | acts ]ₙ->*
  (fun _ _ => [], 0 : inl ([], EPid 1, [], [], false) ||||
       1 : inl ([], EPid 1, [], [], false) |||| nullpool).
Proof.
  eexists. exists 26.
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_local. apply step_concbif. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor; auto.
    do 2 constructor. intros. simpl in H.
    inversion H; subst; cbn. 2: inversion H1.
    constructor. repeat constructor. intros. simpl in H0. inversion H0.
    simpl. repeat constructor. inversion H1.
    inversion H2; subst.
    repeat constructor.
    inversion H4; subst.
    auto.
  eapply n_trans. eapply n_spawn with (ι := 0) (ι' := 1); simpl. 2: reflexivity.
    2: constructor. all: simpl; auto.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  rewrite par_swap with (ι' := 1). 2: lia.

  eapply n_trans. eapply n_other with (ι := 1).
    repeat constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    repeat constructor. simpl. auto.

  rewrite par_swap with (ι' := 0). 2: lia.

  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    repeat constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0) (a := ASelf 0).
    constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0) (ι' := 1).
    constructor. constructor. simpl.
  eapply n_trans. eapply n_other with (ι := 0); cbn; try reflexivity.
    repeat constructor. simpl. auto.

  simpl.
  rewrite par_swap with (ι' := 1). 2: lia.

  eapply n_trans. apply n_arrive with (ι0 := 0).
    reflexivity. repeat constructor.
  cbn.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_receive; auto; try reflexivity. right. right. left. eexists. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1) (a := ASelf 1).
    constructor. auto.
  eapply n_trans. eapply n_send with (ι := 1) (ι' := 0).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply n_trans. apply n_arrive with (ι0 := 1).
    reflexivity. repeat constructor.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_receive; auto. reflexivity. right. right. left. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  cbn. break_match_goal. 2: congruence.
  repeat ether_cleanup.
  apply n_refl.
Qed.

Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELit 2%Z, [], [], false) ||||
       1 : inl ([], ELit 2%Z, [], [], false) ||||
       2 : inl ([], ELit 3%Z, [], [], false) ||||
       3 : inl ([], ELit 5%Z, [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], nullpool).
Proof.
  exists 8. eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite par_swap with (ι := 0) (ι' := 1).
  rewrite par_swap with (ι := 0) (ι' := 2).
  rewrite par_swap with (ι := 0) (ι' := 3). 2-4: lia.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite par_swap with (ι := 1) (ι' := 2).
  rewrite par_swap with (ι := 1) (ι' := 3). 2-3: lia.
  eapply n_trans. eapply n_other with (ι := 2).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite par_swap with (ι := 2) (ι' := 3). 2: lia.
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  repeat rewrite nullpool_remove.
  apply n_refl.
Qed.

(* trapping kill which comes from link *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF link [EPid 1])
                             (EConcBIF exit [kill]), [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EVar 0)], [], [], true) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 1 : inl ([], VCons (EXIT) (VCons (EPid 0) (VCons kill ENil)), [], [0], true)
           |||| nullpool).
Proof.
  do 2 eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_link.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_exit_self. constructor. auto.
  simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_dead.
  simpl.
  eapply n_trans. apply n_terminate.
    rewrite par_swap. rewrite nullpool_remove. 2: lia.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    reflexivity.
    do 2 constructor.
  cbn.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    do 2 constructor.
    eapply p_exit_convert. right. split; auto. now constructor.
  cbn.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_receive; try reflexivity. do 2 right. left. eexists. reflexivity.
  cbn. break_match_goal. 2: congruence.
  ether_cleanup.
  apply n_refl.
Qed.

(* kill through link, without traps -> no conversion to killed *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF link [EPid 1])
                             (EConcBIF exit [kill]), [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 1 : inr [(0, kill)]
           |||| nullpool).
Proof.
  do 2 eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_link.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_exit_self. constructor. auto.
  simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_dead.
  simpl.
  eapply n_trans. apply n_terminate.
    rewrite par_swap. rewrite nullpool_remove. 2: lia.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    reflexivity.
    do 2 constructor.
  cbn.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    do 2 constructor.
  eapply p_exit_terminate. right. left. repeat split; auto.
    1-3: intros; try congruence. now constructor.
  cbn.
  ether_cleanup.
  apply n_refl.
Qed.

(* kill sent explicitly, converted to killed *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF link [EPid 1])
                             (ELet "X" (EConcBIF exit [EPid 1; kill])
                                       (EReceive [(PVar, ENil)])), [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 0 : inr [(1, killed)]
           |||| nullpool).
Proof.
  do 2 eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_link.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0).
    apply p_exit. constructor.
  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  simpl.
  rewrite par_swap. 2: lia.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    reflexivity.
    do 2 constructor.
  cbn.
  eapply n_trans. eapply n_arrive with (ι0 := 0).
    reflexivity.
    apply p_exit_terminate. auto.
  cbn.
  eapply n_trans. apply n_send.
    apply p_dead. simpl.
  eapply n_trans. apply n_terminate.
    ether_cleanup.
    rewrite par_swap with (p := None). rewrite nullpool_remove. 2: lia.
  eapply n_trans. eapply n_arrive with (ι0 := 1).
    reflexivity.
    apply p_exit_terminate.
    right. left. intuition; auto. congruence.
  cbn.
  repeat ether_cleanup.
  apply n_refl.
Qed.

(* trapping exits *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], EReceive [(PVar, EConcBIF exit [EPid 1; ELit "foo"])], [], [], false) ||||
       1 : inl ([], ELet "X" (ELet "X" (EConcBIF process_flag [trap_exit; tt]) 
                                       (EConcBIF send [EPid 0; ENil])) 
                             (EReceive [(PVar, EVar 0)]), [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 1 : inl ([], VCons EXIT (VCons (EPid 0) (VCons (ELit "foo") ENil)), [], [], true)
           |||| nullpool).
Proof.
  do 2 eexists.
  rewrite par_swap. 2: lia.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    eapply p_set_flag. reflexivity. auto.
  cbn.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 1).
    do 3 constructor. simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    do 3 constructor. auto. simpl.
  rewrite par_swap. 2: lia.
  eapply n_trans. eapply n_arrive with (ι0 := 1).
    reflexivity.
    do 2 constructor.
  cbn.
  eapply n_trans. eapply n_other.
    apply p_receive. 1-2: reflexivity. do 2 right. left. now eexists.
  cbn. break_match_goal. 2: congruence.
  eapply n_trans. eapply n_other.
    do 3 constructor. auto.
  eapply n_trans. eapply n_other.
    do 3 constructor. auto.
  eapply n_trans. eapply n_other.
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send.
    do 3 constructor. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. apply n_terminate.
  rewrite par_swap, nullpool_remove. 2: lia.
  eapply n_trans. apply n_arrive with (ι0 := 0).
    reflexivity.
    apply p_exit_convert. left. split; auto. congruence.
  cbn.
  eapply n_trans. apply n_other.
    apply p_receive. 1-2: reflexivity. do 2 right; left; now eexists.
  cbn. break_match_goal. 2: congruence.
  ether_cleanup.
  apply n_refl.
Qed.

(* explicit exit signal drop *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELet "X" (EConcBIF exit [EPid 1; ELit "normal"]) 
                             (EConcBIF send [EPid 1; ENil]), [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 0 : inl ([], ENil, [], [], false) ||||
       1 : inl ([], ENil, [], [], false) |||| nullpool).
Proof.
  do 2 eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_send with (ι := 0).
    do 3 constructor. simpl.
  rewrite par_swap. 2: lia.
  eapply n_trans. apply n_arrive with (ι0 := 0).
    do 2 constructor.
    apply p_exit_drop. left. auto.
  cbn.
  eapply n_trans. apply n_arrive with (ι0 := 0).
    do 2 constructor.
    apply p_arrive; constructor.
  cbn.
  eapply n_trans. apply n_other.
    apply p_receive. 1-2: reflexivity. do 2 right; left; now eexists.
  cbn. break_match_goal. 2: congruence.
  rewrite par_swap. 2: lia.
  ether_cleanup.
  apply n_refl.
Qed.

(* implicit exit signal drop *)
Goal exists k acts,
  (fun _ _ => [], 0 : inl ([], ELet "X" (ELit 1%Z) (EVar 0), [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  (fun _ _ => [], 1 : inl ([], EReceive [(PVar, EVar 0)], [], [], false) |||| nullpool).
Proof.
  do 2 eexists.
  eapply n_trans. eapply n_other.
    do 3 constructor. auto.
  eapply n_trans. eapply n_other.
    do 3 constructor. auto. simpl.
  eapply n_trans. eapply n_other.
    apply p_terminate. constructor. auto.
  eapply n_trans. eapply n_terminate.
  rewrite par_swap, nullpool_remove. 2: lia.
  (* cannot make more steps here *)
  apply n_refl.
Qed.

Close Scope string_scope.
