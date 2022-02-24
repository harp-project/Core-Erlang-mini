Require Import ConcurrentFunSemantics.
Import ListNotations.
(*
  0 -[ 1 + 1 ]-> 1
  1 -[ 2 ]-> 3
  2 -[ 3 ]-> 3
  3 : 2 + 3 == 5
*)
Open Scope string_scope. Print LiveProcess.
Goal exists acts k,
  ([], 0 : inl ([], EConcBIF (ELit "send") [EPid 1;EPlus (ELit 1%Z) (ELit 1%Z)], [], [], false) ||||
       1 : inl ([], EReceive [(PVar, EConcBIF (ELit "send") [EPid 3;EVar 0])], [], [], false) ||||
       2 : inl ([], EConcBIF (ELit "send") [EPid 3;ELit 3%Z], [], [], false) ||||
       3 : inl ([], EReceive [(PVar, EReceive [(PVar, EPlus (EVar 0) (EVar 1))])], [], [], false) |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : inl ([], ELit 2%Z, [], [], false) ||||
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
  eapply n_trans. apply n_arrive. 
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0). 2-3: lia.

  (* Again with 0 *)

  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 1). 2-3: lia.

  eapply n_trans. eapply n_send with (ι := 0) (ι' := 1).
  constructor. constructor. simpl.

  rewrite par_swap with (ι' := 1). 2: lia.
  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.

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

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
    cbn. break_match_goal. 2: congruence.

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
  ([], 0 : inl ([], ELet "X" (EConcBIF (ELit "spawn") [EFun [] (EReceive [(PVar, EConcBIF (ELit "send") [EVar 0; EConcBIF (ELit "self") []])]);
                                             ENil])
             (ELet "Y"%string (EConcBIF (ELit "send") [EVar 0; EConcBIF (ELit "self") []])
                 (EReceive [(PVar, EVar 0)]))
                  , [], [], false)
  |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : inl ([], EPid 1, [], [], false) ||||
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

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.
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

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_receive; auto. reflexivity. right. right. left. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  cbn. break_match_goal. 2: congruence.
  break_match_goal. 2: congruence.
  apply n_refl.
Qed.

Goal exists k acts,
  ([], 0 : inl ([], ELit 2%Z, [], [], false) ||||
       1 : inl ([], ELit 2%Z, [], [], false) ||||
       2 : inl ([], ELit 3%Z, [], [], false) ||||
       3 : inl ([], ELit 5%Z, [], [], false) |||| nullpool)
  -[k | acts]ₙ->*
  ([], nullpool).
Proof.
  exists 8. eexists.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite update_swap with (ι := 0) (ι' := 1).
  rewrite update_swap with (ι := 0) (ι' := 2).
  rewrite update_swap with (ι := 0) (ι' := 3). 2-4: lia.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite update_swap with (ι := 1) (ι' := 2).
  rewrite update_swap with (ι := 1) (ι' := 3). 2-3: lia.
  eapply n_trans. eapply n_other with (ι := 2).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  rewrite update_swap with (ι := 2) (ι' := 3). 2: lia.
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_terminate; auto. auto.
  eapply n_trans. apply n_terminate.
  simpl.

  repeat rewrite nullpool_remove.
  apply n_refl.
Qed.

Close Scope string_scope.
