(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.

Import ListNotations.

Definition Mailbox : Set := list Exp.
Definition Process : Set := FrameStack * Exp * Mailbox.

Inductive Action : Set :=
| ASend (p : PID) (t : Exp)
| AReceive (t : Exp)
| AArrive (t : Exp)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Exp)
| AInternal.

Fixpoint find_clause (v : Exp) (c : list (Pat * Exp)) : option (Exp * list Exp) :=
match c with
| [] => None
| (p, e)::xs => match match_pattern p v with
                | None => find_clause v xs
                | Some l => Some (e, l)
                end
end.

Fixpoint receive (m : Mailbox) (c : list (Pat * Exp)) : option (Exp * Exp * list Exp) :=
match m with
| [] => None
| m::ms => match find_clause m c with
           | Some (e, l) => Some (m, e, l)
           | None => receive ms c
           end
end.

Fixpoint removeFirst {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
                     (x : A) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | y :: tl => if eq_dec x y then tl else y :: removeFirst eq_dec x tl
  end.

Definition pop (v : Exp) (m : Mailbox) := removeFirst Exp_eq_dec v m.

Fixpoint len (l : Exp) : option nat :=
match l with
| ENil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.

Fixpoint mk_list (l : Exp) : option (list Exp) :=
match l with
| ENil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
Inductive processLocalSemantics : Process -> Action -> Process -> Prop :=
| p_local fs e fs' e' mb :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  (fs, e, mb) -⌈ AInternal ⌉-> (fs', e', mb)

| p_send_local1 fs e ι mb :
  (fs, ESend ι e, mb) -⌈ AInternal ⌉-> (FSend1 e :: fs, ι, mb)
| p_send_local2 fs e v mb : VALCLOSED v ->
  (FSend1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSend2 v :: fs, e, mb)
| p_spawn_local1 fs e ι mb :
  (fs, ESpawn ι e, mb) -⌈ AInternal ⌉-> (FSpawn1 e :: fs, ι, mb)
| p_spawn_local2 fs e v mb : VALCLOSED v ->
  (FSpawn1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSpawn2 v :: fs, e, mb)


| p_arrive mb mb' fs e v : VALCLOSED v -> mb' = mb ++ [v] ->
  (fs, e, mb) -⌈ AArrive v ⌉-> (fs, e, mb')

| p_send ι v mb fs : VALCLOSED v ->
  (FSend2 (EPid ι) :: fs, v, mb) -⌈ ASend ι v ⌉-> (fs, v, mb)

| p_self ι fs mb :
  ( fs, ESelf, mb ) -⌈ ASelf ι ⌉-> ( fs, EPid ι, mb )

| p_spawn ι fs mb vl e l:
  Some (length vl) = len l -> VALCLOSED l ->
  (FSpawn2 (EFun vl e) :: fs, l, mb) -⌈ASpawn ι (EFun vl e) l⌉-> (fs, EPid ι, mb)

| p_receive mb l fs e m mb' bindings :
  receive mb l = Some (m, e, bindings) -> mb' = pop m mb
->
  (fs, EReceive l, mb) -⌈ AReceive m ⌉-> (fs, e.[list_subst bindings idsubst], mb')

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> nat -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x 0 [] x
| lsstep x l ls y z k : r x l y -> LabelStar r y k ls z -> LabelStar r x (S k) (l::ls) z.

Notation "x -⌈ k | xs ⌉-> y" := (LabelStar processLocalSemantics x k xs y) (at level 50).

(******************************************************************************)
(****************************   NODES  ****************************************)
(******************************************************************************)

Definition GlobalMailbox : Set := list (PID * Exp).
Definition ProcessPool : Set := (PID -> option Process).
Definition Node : Set := GlobalMailbox * ProcessPool.

Definition nullpool : ProcessPool := fun ι => None.
Definition par (pid : PID) (proc: Process) (n : ProcessPool) : ProcessPool :=
  fun ι => if Nat.eq_dec pid ι then Some proc else n ι.

Notation "pid : p |||| n" := (par pid p n) (at level 30, right associativity).
Lemma par_same :  forall ι p p' Π, ι : p |||| ι : p' |||| Π = ι : p |||| Π.
Proof.
  intros. unfold par. extensionality ι'.
  break_match_goal; auto.
Qed.

Lemma par_swap :  forall ι ι' p p' Π, ι <> ι' ->
   ι : p |||| ι' : p' |||| Π = ι' : p' |||| ι : p |||| Π.
Proof.
  intros. unfold par. extensionality ι''.
  break_match_goal; auto.
  subst. break_match_goal; auto. congruence.
Qed.

Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
| nsend p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι' t⌉-> p'
->
  (ether, ι : p |||| prs) -[ASend ι' t | ι]ₙ->  (ether ++ [(ι', t)], ι : p' |||| prs)

(** This leads to the loss of determinism: *)
| narrive ι p p' ether prs t:
  In (ι, t) ether ->
  p -⌈AArrive t⌉-> p' ->
  (ether, ι : p |||| prs) -[AArrive t | ι]ₙ-> (removeFirst (prod_eqdec Nat.eq_dec Exp_eq_dec) (ι, t) ether,
                                            ι : p' |||| prs)

| nother p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = AInternal \/ a = ASelf ι \/ (exists t, a = AReceive t))
->
   (ether, ι : p |||| Π) -[a| ι]ₙ-> (ether, ι : p' |||| Π)

| nspawn Π p p' v1 v2 l ι ι' ether:
  mk_list v2 = Some l -> (ι : p |||| Π) ι' = None ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι : p |||| Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' : ([], EApp v1 l, []) |||| ι : p' |||| Π)

(* | nsend1 p p' q q' Π (ι ι' : PID) t :
  p -⌈ASend ι' t⌉-> p' -> q -⌈AArrive t⌉-> q' -> ι <> ι'
->
  ι : p |||| ι' : q |||| Π -[ASend ι' t | ι]ₙ-> ι : p' |||| ι' : q' |||| Π

| nsend2 p p' p'' t (ι : PID) Π :
  p -⌈ASend ι t⌉-> p' -> p' -⌈AArrive t⌉-> p'' (** two transitions, because this is atomic! *)
->
   ι : p |||| Π  -[ASend ι t | ι]ₙ->  ι : p'' |||| Π 

| nsend3 p p' (ι ι' : PID) Π t :
  p -⌈ASend ι' t⌉-> p' -> (ι : p |||| Π) ι = None
->
  ι : p |||| Π -[ASend ι' t | ι]ₙ-> ι : p' |||| Π *)
(* | nreceive p p' t Π (ι : PID) :
  p -⌈AReceive t⌉-> p'
->
   ι : p |||| Π -[AReceive t | ι]ₙ-> ι : p' |||| Π

| ninternal p p' Π (ι : PID) :
  p -⌈AInternal⌉-> p'
->
   ι : p |||| Π -[AInternal | ι]ₙ-> ι : p' |||| Π

| nself p p' Π ι:
  p -⌈ASelf ι⌉-> p'
->
  ι : p |||| Π -[ASelf ι | ι]ₙ-> ι : p' |||| Π *)

(* *)
where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

(*
Fixpoint Pat_eqb (p1 p2 : Pat) : bool :=
match p1, p2 with
 | PLit l, PLit l2 => Z.eqb l l2
 | PPid p, PPid p2 => p =? p2
 | PVar, PVar => true
 | PNil, PNil => true
 | PCons p1 p2, PCons p12 p22 => Pat_eqb p1 p12 && Pat_eqb p2 p22
 | _, _ => false
end.

Fixpoint list_eqb {A} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Fixpoint Exp_eqb (e1 e2 : Exp) : bool :=
match e1, e2 with
 | ELit l, ELit l2 => Z.eqb l l2
 | EPid p, EPid p2 => p =? p2
 | EVar n, EVar n2 => n =? n2
 | EFunId n, EFunId n2 => n =? n2
 | EFun vl e, EFun vl2 e2 => list_eqb String.eqb vl vl2 && Exp_eqb e e2
 | EApp exp l, EApp exp2 l2 => Exp_eqb exp exp2 && list_eqb Exp_eqb l l2
 | ELet v e1 e2, ELet v2 e12 e22 => Exp_eqb e1 e12 && Exp_eqb e12 e22
 | ELetRec f vl b e, ELetRec f2 vl2 b2 e2 => _
 | EPlus e1 e2, EPlus e12 e22 => _
 | ECase e0 p e1 e2, ECase e02 p2 e12 e22 => _
 | ECons e1 e2, ECons e12 e22 => _
 | ENil, ENil => true
 | VCons e1 e2, VCons e12 e22 => _
 | ESend p e, ESend p2 e2 => _
 | EReceive l, EReceive l2 => _
 | _, _ => false
end. *)
(* 
Fixpoint list_eq_Node (l : list (PID * Process)) (n : Node) : Prop :=
match l with
| [] => True
| (p, pr)::xs => find p n = Some pr /\ list_eq_Node xs n
end.

Definition equivalent (n1 n2 : Node) : Prop :=
match n1 with
| {| this := x; sorted := y |} => length n2 = length x /\ list_eq_Node x n2
end. *)

(* #[export] Instance processEq : Equiv Process := eq. *)

Reserved Notation "n -[ k | l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> nat -> list (Action * PID) -> Node -> Prop :=
| nrefl n (* n'  *): (* Permutation n n' -> *) n -[ 0 | [] ]ₙ->* n (* ' *)
| ntrans n n' n'' k l a ι:
  n -[a|ι]ₙ-> n' -> n' -[k|l]ₙ->* n''
->
  n -[S k | (a,ι)::l]ₙ->* n''
where "n -[ k | l ]ₙ->* n'" := (closureNodeSem n k l n').

(*
  0 -[ 1 + 1 ]-> 1
  1 -[ 2 ]-> 3
  2 -[ 3 ]-> 3
  3 : 2 + 3 == 5
*)
Goal exists acts k,
  ([], 0 : ([], ESend (EPid 1) (EPlus (ELit 1) (ELit 1)), []) ||||
       1 : ([], EReceive [(PVar, ESend (EPid 3) (EVar 0))], []) ||||
       2 : ([], ESend (EPid 3) (ELit 3), []) ||||
       3 : ([], EReceive [(PVar, EReceive [(PVar, EPlus (EVar 0) (EVar 1))])], []) |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : ([], ELit 2, []) ||||
       1 : ([], ELit 2, []) ||||
       2 : ([], ELit 3, []) ||||
       3 : ([], ELit 5, []) |||| nullpool).
Proof.
  eexists. exists 21.
  (* Some steps with 0 *)
  eapply ntrans. eapply nother with (ι := 0).
    apply p_send_local1. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_send_local2. constructor. auto.
  eapply ntrans. eapply nother with (ι := 0).
    constructor. constructor. auto.
  eapply ntrans. eapply nother with (ι := 0).
    do 3 constructor. auto.

  rewrite par_swap with (ι' := 2). rewrite par_swap with (ι' := 2). 2-3: lia.

  (* Some steps with 2 *)
  eapply ntrans. eapply nother with (ι := 2).
    apply p_send_local1. auto.
  eapply ntrans. eapply nother with (ι := 2).
    apply p_send_local2. constructor. auto.

  rewrite par_swap with (ι' := 3). rewrite par_swap with (ι' := 3). 2-3: lia.

  eapply ntrans. eapply nsend with (ι := 2) (ι' := 3).
    constructor. constructor.
  simpl.

  rewrite par_swap with (ι' := 3). 2: lia.
  eapply ntrans. apply narrive. 
    constructor. reflexivity. repeat constructor.
  simpl. break_match_goal. 2: congruence.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0). 2-3: lia.

  (* Again with 0 *)
  eapply ntrans. eapply nother with (ι := 0).
  constructor. constructor. auto.

  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 1). 2-3: lia.

  eapply ntrans. eapply nsend with (ι := 0) (ι' := 1).
  constructor. constructor. simpl.

  rewrite par_swap with (ι' := 1). 2: lia.
  eapply ntrans. apply narrive.
    constructor. reflexivity. repeat constructor.
  simpl. break_match_goal. 2: congruence.

  (* Now with 1 *)
  eapply ntrans. eapply nother with (ι := 1).
    apply p_receive; try reflexivity. right. right. eexists. auto.
  simpl.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_send_local1. auto.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_send_local2. constructor. auto.

  cbn. break_match_goal. 2: congruence.
  rewrite par_swap with (ι' := 3). 2: lia.

  eapply ntrans. eapply nsend with (ι := 1) (ι' := 3).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 3). 2: lia.

  eapply ntrans. apply narrive.
    constructor. reflexivity. repeat constructor.
    simpl. break_match_goal. 2: congruence.

  (* Mailbox processing for 3 *)
  eapply ntrans. eapply nother with (ι := 3).
    apply p_receive; try reflexivity. right. right. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  eapply ntrans. eapply nother with (ι := 3).
    apply p_receive; try reflexivity. right. right. eexists. auto.
    cbn. break_match_goal. 2: congruence.

  eapply ntrans. eapply nother with (ι := 3).
    constructor. constructor. auto.
  eapply ntrans. eapply nother with (ι := 3).
    constructor. constructor. constructor. auto.
  eapply ntrans. eapply nother with (ι := 3).
    constructor. constructor. auto.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0).
  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 2).

  apply nrefl.
  all: lia.
Qed.

(*

let X = spawn(fun() -> receive X -> X ! self() end end, [])
  in let Y = X ! self()
    in receive X -> X end

*)
Goal exists acts k,
  ([], 0 : ([], ELet "X"%string (ESpawn (EFun [] (EReceive [(PVar, ESend (EVar 0) ESelf)]
                                            )) ENil)
             (ELet "Y"%string (ESend (EVar 0) ESelf)
                 (EReceive [(PVar, EVar 0)]))
                  , [])
  |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : ([], EPid 1, []) ||||
       1 : ([], EPid 1, []) |||| nullpool).
Proof.
  eexists. exists 21.
  eapply ntrans. eapply nother with (ι := 0).
    do 2 constructor. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_spawn_local1. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_spawn_local2. do 2 constructor. intros.
    inversion H; subst; cbn. 2: inversion H1. repeat constructor.
    auto.
  eapply ntrans. eapply nspawn with (ι := 0) (ι' := 1); simpl. 2: reflexivity.
    2: constructor. all: simpl; auto. constructor.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply ntrans. eapply nother with (ι := 0).
    do 3 constructor. auto.

  rewrite par_swap with (ι' := 1). 2: lia.

  eapply ntrans. eapply nother with (ι := 1).
    repeat constructor. auto.
  eapply ntrans. eapply nother with (ι := 1).
    repeat constructor. simpl. auto.

  rewrite par_swap with (ι' := 0). 2: lia.

  simpl.
  eapply ntrans. eapply nother with (ι := 0).
    repeat constructor. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_send_local1. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_send_local2. constructor. auto.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_self. auto.
  eapply ntrans. eapply nsend with (ι := 0) (ι' := 1).
    constructor. constructor. simpl.
  eapply ntrans. eapply nother with (ι := 0); cbn; try reflexivity.
    repeat constructor. simpl. auto.

  rewrite par_swap with (ι' := 1). 2: lia.

  eapply ntrans. apply narrive.
    constructor. reflexivity. repeat constructor.
  simpl. break_match_goal. 2: congruence.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_receive; auto; try reflexivity. right. right. eexists. auto.
  simpl.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_send_local1. auto.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_send_local2. constructor. auto.
  eapply ntrans. eapply nother with (ι := 1).
    apply p_self. auto.
  eapply ntrans. eapply nsend with (ι := 1) (ι' := 0).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply ntrans. apply narrive.
    constructor. reflexivity. repeat constructor.
  eapply ntrans. eapply nother with (ι := 0).
    apply p_receive; auto. reflexivity. right. right. eexists. auto. simpl.
  break_match_goal. 2: congruence.
  cbn. break_match_goal. 2: congruence.
  break_match_goal. 2: congruence.
  apply nrefl.
Qed.

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
