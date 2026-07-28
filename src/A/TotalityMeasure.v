From CoreErlang.A Require Import Syntax.
From Coq Require Import Lia.

Import ListNotations.
Open Scope sub_scope.

(**
  Totality of [normalize_exp] / [normalize_val] / [introduce_let] on
  [EReceive]-free inputs.

  [normalize_exp], [normalize_val] and [introduce_let] are defined with an
  explicit fuel parameter because they are not visibly structurally
  recursive: heat steps move code between the focus and the [FrameStack],
  and [introduce_let] can hand off to a renamed continuation. This file
  supplies the fuel bound that makes them total.

  A naive size measure (size of focus + size of context) turns out to be
  *exactly flat* across several real transitions of the machine, not just
  close:
    - shifting the head of a pending argument/BIF list into focus
      ([FApp1 (f :: args) -> FApp2], the [FApp2]/[FBIF2] todo-shift,
      [FCons1 -> FCons2]) replaces one frame with another of equal
      bookkeeping weight;
    - handing off between [normalize_exp], [normalize_val] and
      [introduce_let] with the *same* continuation ([VVal v ->
      normalize_val], [introduce_let]'s [is_value] and renaming branches)
      doesn't touch the frame stack or shrink anything.
  Since the fuel argument drops by exactly 1 on every recursive call
  regardless, a measure that is flat at these points cannot drive a
  strong induction on fuel - every single recursive call needs strict
  decrease, not just "eventually".

  The fix is a 3-level lexicographic measure, collapsed into one [nat]
  via [encode]:
    1. [M1] - weighted size (every stored/focused subexpression costs
       [2 * size_exp], every frame carries a flat [+1] tag). Strictly
       decreases whenever a real AST constructor is consumed (heat steps)
       or a frame is fully resolved with nothing replacing it. Never
       increases, but ties exactly at frame-replacement steps and at
       cross-function handoffs.
    2. [len_fs] - total remaining pending-list length (counting
       [FCons1] as a virtual length-1 list). Strictly decreases whenever
       [M1] ties due to a frame replacement.
    3. [phase] - a 3-valued tag ([VAL < EXP < IL]). Strictly decreases
       whenever [M1] *and* [len_fs] both tie, which only happens on
       same-continuation handoffs between the three functions.

  [EReceive] can only ever cause [None] (via [normalize_exp]'s own
  [EReceive _ => None] arm), and none of these functions ever synthesize
  a fresh [EReceive] - they only ever combine existing, already-checked
  parts. So the totality statement is conditioned on the input being
  [EReceive]-free ([no_receive_exp]/[no_receive_fs]), and the induction
  carries that invariant through every recursive call, concluding that
  the result is [EReceive]-free too (needed e.g. to justify the
  [VFun]-body call feeding back into [normalize_val]).
*)

(* ----------------------------------------------------------------- *)
(** * Size/weight measure infrastructure *)

Definition sum_size (l : list Exp) : nat := foldr (fun x acc => size_exp x + acc) 0 l.

(* Every frame carries a flat [+1] tag (spent, with nothing to replace it,
   whenever a frame is popped without a new frame taking its place); every
   not-yet-processed subexpression stored in a frame costs the same [2x]
   weight it would cost as a fresh focus, matching [focus_weight] below. *)
Definition frame_size (f : Frame) : nat :=
  match f with
  | FLet e2 => 1 + 2 * size_exp e2
  | FCase p e2 e3 => 1 + 2 * size_exp e2 + 2 * size_exp e3
  | FApp1 args => 1 + 2 * sum_size args
  | FApp2 _ _ todo => 1 + 2 * sum_size todo
  | FBIF1 args => 1 + 2 * sum_size args
  | FBIF2 _ _ todo => 1 + 2 * sum_size todo
  | FCons1 e1 => 1 + 2 * size_exp e1
  | FCons2 _ => 1
  end.

Definition size_fs (k : FrameStack) : nat := foldr (fun f acc => frame_size f + acc) 0 k.

(* Remaining pending-list length per frame; [FCons1] is treated as a
   virtual length-1 list since it behaves exactly like a singleton
   App/BIF argument list for the purposes of the todo-shift argument. *)
Definition frame_len (f : Frame) : nat :=
  match f with
  | FApp1 args => length args
  | FApp2 _ _ todo => length todo
  | FBIF1 args => length args
  | FBIF2 _ _ todo => length todo
  | FCons1 _ => 1
  | _ => 0
  end.

Definition len_fs (k : FrameStack) : nat := foldr (fun f acc => frame_len f + acc) 0 k.

(* Matches [normalize_exp]'s own case split: a [VFun] needs its body fully
   processed (size-proportional work via a *fresh* stack), any other
   value delegates to [normalize_val] in O(1) (no further decomposition),
   and a compound expression needs its usual [2x] traversal weight. *)
Definition focus_weight (e : Exp) : nat :=
  match e with
  | VVal (VFun vl body) => 2 * size_exp body + 2
  | VVal _ => 0
  | EExp _ => 2 * size_exp e
  end.

Definition M1_exp (e : Exp) (k : FrameStack) : nat := focus_weight e + size_fs k.
Definition M1_val (v : Val) (k : FrameStack) : nat := size_fs k.
Definition M1_il  (e : Exp) (k : FrameStack) : nat := size_fs k.

Lemma size_exp_ge_1 : forall e, 1 <= size_exp e.
Proof. intros e; destruct e; cbn; lia. Qed.

Lemma focus_weight_le : forall e, focus_weight e <= 2 * size_exp e.
Proof.
  intros e. destruct e as [nv | v]; cbn.
  - lia.
  - destruct v; cbn; lia.
Qed.

Lemma length_le_sum_size : forall l, length l <= sum_size l.
Proof.
  induction l as [|x xs IH]; cbn; [lia|].
  unfold sum_size in *. cbn.
  pose proof (size_exp_ge_1 x). lia.
Qed.

Lemma len_fs_le_size_fs : forall k, len_fs k <= size_fs k.
Proof.
  induction k as [| f k IH]; cbn in *; [lia|].
  unfold len_fs, size_fs in IH.
  destruct f as [args|v l1 l2|e2|p e2 e3|e1|v2|args|v l1 l2];
    cbn; unfold sum_size in *.
  - pose proof (length_le_sum_size args). unfold sum_size in *. lia.
  - pose proof (length_le_sum_size l2). unfold sum_size in *. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - pose proof (length_le_sum_size args). unfold sum_size in *. lia.
  - pose proof (length_le_sum_size l2). unfold sum_size in *. lia.
Qed.

(* ----------------------------------------------------------------- *)
(** * Per-transition [M1] / [len_fs] decrease facts *)

(* Heat steps: consuming the top-level constructor's own tag always pays
   for exactly 1 unit of decrease, regardless of argument-list length. *)
Lemma heat_elet : forall e1 e2 k,
  M1_exp e1 (FLet e2 :: k) < M1_exp (ELet e1 e2) k.
Proof. intros. unfold M1_exp, size_fs; cbn. pose proof (focus_weight_le e1). lia. Qed.

Lemma heat_ecase : forall e0 p e1 e2 k,
  M1_exp e0 (FCase p e1 e2 :: k) < M1_exp (ECase e0 p e1 e2) k.
Proof. intros. unfold M1_exp, size_fs; cbn. pose proof (focus_weight_le e0). lia. Qed.

Lemma heat_eapp : forall f args k,
  M1_exp f (FApp1 args :: k) < M1_exp (EApp f args) k.
Proof. intros. unfold M1_exp, size_fs; cbn. unfold sum_size. pose proof (focus_weight_le f). lia. Qed.

Lemma heat_ebif : forall f args k,
  M1_exp f (FBIF1 args :: k) < M1_exp (EBIF f args) k.
Proof. intros. unfold M1_exp, size_fs; cbn. unfold sum_size. pose proof (focus_weight_le f). lia. Qed.

Lemma heat_econs : forall e1 e2 k,
  M1_exp e2 (FCons1 e1 :: k) < M1_exp (ECons e1 e2) k.
Proof. intros. unfold M1_exp, size_fs; cbn. pose proof (focus_weight_le e2). lia. Qed.

(* Frame fully consumed, nothing replaces it: the frame's flat [+1] tag is
   pure profit. *)
Lemma let_pop : forall (v : Val) (e2 : Exp) (k' : FrameStack),
  M1_exp e2 k' < M1_val v (FLet e2 :: k').
Proof. intros. unfold M1_exp, M1_val, size_fs; cbn. pose proof (focus_weight_le e2). lia. Qed.

Lemma il_let_pop : forall e e2 k',
  M1_exp e2 k' < M1_il e (FLet e2 :: k').
Proof. intros. unfold M1_exp, M1_il, size_fs; cbn. pose proof (focus_weight_le e2). lia. Qed.

Lemma case_reduce : forall (v : Val) (e1 e2 : Exp) (p : Pat) (k' : FrameStack),
  M1_exp e1 k' < M1_val v (FCase p e1 e2 :: k')
  /\ M1_exp e2 k' < M1_val v (FCase p e1 e2 :: k').
Proof.
  intros. unfold M1_exp, M1_val, size_fs; cbn.
  pose proof (focus_weight_le e1). pose proof (focus_weight_le e2). split; lia.
Qed.

Lemma fapp1_empty_to_il : forall (v : Val) (k' : FrameStack),
  M1_il (EApp (VVal v) []) k' < M1_val v (FApp1 [] :: k').
Proof. intros. unfold M1_il, M1_val, size_fs; cbn. unfold sum_size. cbn. lia. Qed.

Lemma fapp2_empty_to_il : forall (v : Val) (f : Val) (done : list Val) (k' : FrameStack),
  M1_il (EApp (VVal f) (map VVal done ++ [VVal v])) k' < M1_val v (FApp2 f done [] :: k').
Proof. intros. unfold M1_il, M1_val, size_fs; cbn. lia. Qed.

Lemma fbif1_empty_to_il : forall (v : Val) (k' : FrameStack),
  M1_il (EBIF (VVal v) []) k' < M1_val v (FBIF1 [] :: k').
Proof. intros. unfold M1_il, M1_val, size_fs; cbn. unfold sum_size. cbn. lia. Qed.

Lemma fbif2_empty_to_il : forall (v : Val) (f : Val) (done : list Val) (k' : FrameStack),
  M1_il (EBIF (VVal f) (map VVal done ++ [VVal v])) k' < M1_val v (FBIF2 f done [] :: k').
Proof. intros. unfold M1_il, M1_val, size_fs; cbn. lia. Qed.

Lemma fcons2_to_il : forall (v v2 : Val) (k' : FrameStack),
  M1_il (VVal (VCons v v2)) k' < M1_val v (FCons2 v2 :: k').
Proof. intros. unfold M1_il, M1_val, size_fs; cbn. lia. Qed.

(* [VFun]'s two internal calls (processing the body with a fresh stack,
   then continuing with the original stack) both strictly decrease. *)
Lemma vfun_calls : forall (vl : nat) (body : Exp) (k : FrameStack),
  M1_exp body [] < M1_exp (VVal (VFun vl body)) k
  /\ M1_val (VFun vl body) k < M1_exp (VVal (VFun vl body)) k.
Proof.
  intros. unfold M1_exp, M1_val, size_fs; cbn [focus_weight size_fs].
  pose proof (focus_weight_le body). unfold M1_exp in *. cbn. split; lia.
Qed.

(* Frame-replacement steps: [M1] only ties (never increases); the
   argument/BIF list strictly shrinks by exactly one element, which
   [len_fs] picks up as the tie-breaker. *)
Lemma fapp1_to_fapp2 :
  forall (fv : Val) (f : Exp) (args : list Exp) (k' : FrameStack),
    M1_exp f (FApp2 fv [] args :: k') <= M1_val fv (FApp1 (f :: args) :: k')
    /\ (M1_exp f (FApp2 fv [] args :: k') = M1_val fv (FApp1 (f :: args) :: k') ->
        len_fs (FApp2 fv [] args :: k') < len_fs (FApp1 (f :: args) :: k')).
Proof.
  intros fv f args k'.
  unfold M1_exp, M1_val, size_fs, len_fs in *; cbn.
  unfold sum_size. pose proof (focus_weight_le f).
  split; [lia | intros _; lia].
Qed.

Lemma fapp2_todo_shift :
  forall (fv prevv : Val) (done : list Val) (x : Exp) (rest : list Exp) (k' : FrameStack),
    M1_exp x (FApp2 fv (done ++ [prevv]) rest :: k') <= M1_val prevv (FApp2 fv done (x :: rest) :: k')
    /\ (M1_exp x (FApp2 fv (done ++ [prevv]) rest :: k') = M1_val prevv (FApp2 fv done (x :: rest) :: k') ->
        len_fs (FApp2 fv (done ++ [prevv]) rest :: k') < len_fs (FApp2 fv done (x :: rest) :: k')).
Proof.
  intros fv prevv done x rest k'.
  unfold M1_exp, M1_val, size_fs, len_fs in *; cbn.
  unfold sum_size. pose proof (focus_weight_le x).
  split; [lia | intros _; lia].
Qed.

Lemma fbif1_to_fbif2 :
  forall (fv : Val) (f : Exp) (args : list Exp) (k' : FrameStack),
    M1_exp f (FBIF2 fv [] args :: k') <= M1_val fv (FBIF1 (f :: args) :: k')
    /\ (M1_exp f (FBIF2 fv [] args :: k') = M1_val fv (FBIF1 (f :: args) :: k') ->
        len_fs (FBIF2 fv [] args :: k') < len_fs (FBIF1 (f :: args) :: k')).
Proof.
  intros fv f args k'.
  unfold M1_exp, M1_val, size_fs, len_fs in *; cbn.
  unfold sum_size. pose proof (focus_weight_le f).
  split; [lia | intros _; lia].
Qed.

Lemma fbif2_todo_shift :
  forall (fv prevv : Val) (done : list Val) (x : Exp) (rest : list Exp) (k' : FrameStack),
    M1_exp x (FBIF2 fv (done ++ [prevv]) rest :: k') <= M1_val prevv (FBIF2 fv done (x :: rest) :: k')
    /\ (M1_exp x (FBIF2 fv (done ++ [prevv]) rest :: k') = M1_val prevv (FBIF2 fv done (x :: rest) :: k') ->
        len_fs (FBIF2 fv (done ++ [prevv]) rest :: k') < len_fs (FBIF2 fv done (x :: rest) :: k')).
Proof.
  intros fv prevv done x rest k'.
  unfold M1_exp, M1_val, size_fs, len_fs in *; cbn.
  unfold sum_size. pose proof (focus_weight_le x).
  split; [lia | intros _; lia].
Qed.

Lemma fcons1_to_fcons2 :
  forall (prevv : Val) (e1 : Exp) (k' : FrameStack),
    M1_exp e1 (FCons2 prevv :: k') <= M1_val prevv (FCons1 e1 :: k')
    /\ (M1_exp e1 (FCons2 prevv :: k') = M1_val prevv (FCons1 e1 :: k') ->
        len_fs (FCons2 prevv :: k') < len_fs (FCons1 e1 :: k')).
Proof.
  intros prevv e1 k'.
  unfold M1_exp, M1_val, size_fs, len_fs in *; cbn.
  pose proof (focus_weight_le e1).
  split; [lia | intros _; lia].
Qed.

(* Cross-function handoffs with the *same* continuation: [M1] and
   [len_fs] both tie exactly, so only the phase tag (below) can decide. *)
Definition phase_val : nat := 0.
Definition phase_exp : nat := 1.
Definition phase_il  : nat := 2.

Lemma vval_delegate :
  forall (v : Val) (k : FrameStack),
    (match v with VFun _ _ => False | _ => True end) ->
    M1_exp (VVal v) k <= M1_val v k
    /\ (M1_exp (VVal v) k = M1_val v k -> phase_val < phase_exp).
Proof.
  intros v k Hnf.
  unfold M1_exp, M1_val, focus_weight.
  destruct v; try (exfalso; exact Hnf); cbn; unfold phase_val, phase_exp; split; intros; lia.
Qed.

Lemma il_is_value_handoff :
  forall (e_arg : Exp) (k : FrameStack),
    (match e_arg with VVal (VFun _ _) => False | VVal _ => True | _ => False end) ->
    M1_exp e_arg k <= M1_il e_arg k
    /\ (M1_exp e_arg k = M1_il e_arg k -> phase_exp < phase_il).
Proof.
  intros e_arg k Hval.
  unfold M1_exp, M1_il, focus_weight.
  destruct e_arg as [nv|v]; [contradiction|].
  destruct v; try contradiction; cbn; unfold phase_exp, phase_il; split; intros; lia.
Qed.

(* ----------------------------------------------------------------- *)
(** * Renaming invariance of the measure *)

Lemma size_exp_rename : forall e r, size_exp (rename r e) = size_exp e.
Proof.
  apply (Exp_ind2
    (fun e => forall r, size_exp (rename r e) = size_exp e)
    (fun v => forall r, size_val (rename_val r v) = size_val v)
    (fun nv => forall r, size_exp (EExp (rename_nonval r nv)) = size_exp (EExp nv))
    (fun xs => forall r,
      foldr (fun x acc => size_exp x + acc) 0 (map (rename r) xs) =
      foldr (fun x acc => size_exp x + acc) 0 xs)
    (fun xs => forall r,
      foldr (fun '(_, x) acc => size_exp x + acc) 0
        (map (fun '(p, x) => (p, rename (uprenn (pat_vars p) r) x)) xs) =
      foldr (fun '(_, x) acc => size_exp x + acc) 0 xs));
    cbn; intros; try reflexivity.
  - now rewrite H.
  - now rewrite H.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H, H0, H1.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
Qed.

Lemma size_val_rename : forall v r, size_val (rename_val r v) = size_val v.
Proof. intros v r. pose proof (size_exp_rename (VVal v) r) as H. cbn in H. lia. Qed.

Lemma sum_size_rename : forall l r, sum_size (map (rename r) l) = sum_size l.
Proof.
  induction l as [|x xs IH]; intros r; cbn; unfold sum_size in *; [reflexivity|].
  cbn. now rewrite size_exp_rename, IH.
Qed.

Lemma frame_size_rename : forall f r, frame_size (rename_frame r f) = frame_size f.
Proof.
  intros f r; destruct f; cbn;
    repeat (rewrite size_exp_rename || rewrite sum_size_rename || rewrite size_val_rename);
    reflexivity.
Qed.

Lemma frame_len_rename : forall f r, frame_len (rename_frame r f) = frame_len f.
Proof. intros f r; destruct f; cbn; now rewrite ?length_map. Qed.

Lemma size_fs_rename : forall k r, size_fs (rename_framestack r k) = size_fs k.
Proof.
  induction k as [|f k IH]; intros r; unfold rename_framestack, size_fs in *; cbn; [reflexivity|].
  now rewrite frame_size_rename, IH.
Qed.

Lemma len_fs_rename : forall k r, len_fs (rename_framestack r k) = len_fs k.
Proof.
  induction k as [|f k IH]; intros r; unfold rename_framestack, len_fs in *; cbn; [reflexivity|].
  now rewrite frame_len_rename, IH.
Qed.

(* ----------------------------------------------------------------- *)
(** * [EReceive]-freedom *)

Fixpoint no_receive_exp (e : Exp) : Prop :=
  match e with
  | EExp nv =>
    match nv with
    | EApp e1 l =>
      no_receive_exp e1 /\
      (fix nr (xs : list Exp) : Prop :=
       match xs with [] => True | x :: xs' => no_receive_exp x /\ nr xs' end) l
    | ELet e1 e2 => no_receive_exp e1 /\ no_receive_exp e2
    | ECase e0 _ e1 e2 => no_receive_exp e0 /\ no_receive_exp e1 /\ no_receive_exp e2
    | ECons e1 e2 => no_receive_exp e1 /\ no_receive_exp e2
    | EBIF e1 l =>
      no_receive_exp e1 /\
      (fix nr (xs : list Exp) : Prop :=
       match xs with [] => True | x :: xs' => no_receive_exp x /\ nr xs' end) l
    | EReceive _ => False
    end
  | VVal v => no_receive_val v
  end
with no_receive_val (v : Val) : Prop :=
  match v with
  | VLit _ => True
  | VPid _ => True
  | VVar _ => True
  | VFun _ e => no_receive_exp e
  | VNil => True
  | VCons v1 v2 => no_receive_val v1 /\ no_receive_val v2
  end.

Fixpoint nr_exps (xs : list Exp) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => no_receive_exp x /\ nr_exps xs'
  end.

Fixpoint nr_vals (xs : list Val) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => no_receive_val x /\ nr_vals xs'
  end.

Lemma inline_nr_exps_eq : forall l,
  (fix nr (xs : list Exp) : Prop := match xs with [] => True | x::xs' => no_receive_exp x /\ nr xs' end) l
  <-> nr_exps l.
Proof. induction l; cbn; [tauto | rewrite IHl; tauto]. Qed.

Lemma no_receive_app_iff : forall e1 l,
  no_receive_exp (EExp (EApp e1 l)) <-> no_receive_exp e1 /\ nr_exps l.
Proof. intros e1 l. cbn. split; intros [H1 H2]; split; auto. Qed.

Lemma no_receive_bif_iff : forall e1 l,
  no_receive_exp (EExp (EBIF e1 l)) <-> no_receive_exp e1 /\ nr_exps l.
Proof. intros e1 l. cbn. split; intros [H1 H2]; split; auto. Qed.

Definition no_receive_frame (f : Frame) : Prop :=
  match f with
  | FApp1 args => nr_exps args
  | FApp2 fv done todo => no_receive_val fv /\ nr_vals done /\ nr_exps todo
  | FLet e2 => no_receive_exp e2
  | FCase p e1 e2 => no_receive_exp e1 /\ no_receive_exp e2
  | FCons1 e1 => no_receive_exp e1
  | FCons2 v2 => no_receive_val v2
  | FBIF1 args => nr_exps args
  | FBIF2 fv done todo => no_receive_val fv /\ nr_vals done /\ nr_exps todo
  end.

Fixpoint no_receive_fs (k : FrameStack) : Prop :=
  match k with
  | [] => True
  | f :: k' => no_receive_frame f /\ no_receive_fs k'
  end.

Lemma no_receive_exp_rename : forall e r, no_receive_exp e -> no_receive_exp (rename r e).
Proof.
  apply (Exp_ind2
    (fun e => forall r, no_receive_exp e -> no_receive_exp (rename r e))
    (fun v => forall r, no_receive_val v -> no_receive_val (rename_val r v))
    (fun nv => forall r, no_receive_exp (EExp nv) -> no_receive_exp (EExp (rename_nonval r nv)))
    (fun xs => forall r, nr_exps xs -> nr_exps (map (rename r) xs))
    (fun xs => True));
    cbn; intuition auto;
    apply inline_nr_exps_eq; apply H0; apply inline_nr_exps_eq; auto.
Qed.

Lemma no_receive_val_rename : forall v r, no_receive_val v -> no_receive_val (rename_val r v).
Proof. intros v r H. pose proof (no_receive_exp_rename (VVal v) r H) as H'. exact H'. Qed.

Lemma nr_exps_rename : forall l r, nr_exps l -> nr_exps (map (rename r) l).
Proof.
  induction l as [|x xs IH]; cbn; intros r H; auto.
  destruct H as [Hx Hxs]. split; [now apply no_receive_exp_rename | now apply IH].
Qed.

Lemma nr_vals_rename : forall l r, nr_vals l -> nr_vals (map (rename_val r) l).
Proof.
  induction l as [|x xs IH]; cbn; intros r H; auto.
  destruct H as [Hx Hxs]. split; [now apply no_receive_val_rename | now apply IH].
Qed.

Lemma no_receive_frame_rename : forall f r, no_receive_frame f -> no_receive_frame (rename_frame r f).
Proof.
  intros f r H; destruct f; cbn in *.
  - now apply nr_exps_rename.
  - destruct H as [Hf [Hd Ht]]. repeat split; auto using no_receive_val_rename, nr_vals_rename, nr_exps_rename.
  - now apply no_receive_exp_rename.
  - destruct H as [H1 H2]. split; now apply no_receive_exp_rename.
  - now apply no_receive_exp_rename.
  - now apply no_receive_val_rename.
  - now apply nr_exps_rename.
  - destruct H as [Hf [Hd Ht]]. repeat split; auto using no_receive_val_rename, nr_vals_rename, nr_exps_rename.
Qed.

Lemma no_receive_fs_rename : forall k r, no_receive_fs k -> no_receive_fs (rename_framestack r k).
Proof.
  induction k as [|f k IH]; intros r H; unfold rename_framestack in *; cbn in *; auto.
  destruct H as [Hf Hk]. split; [now apply no_receive_frame_rename | now apply IH].
Qed.

Lemma nr_exps_app : forall l1 l2, nr_exps (l1 ++ l2) <-> nr_exps l1 /\ nr_exps l2.
Proof.
  induction l1 as [|x xs IH]; cbn; intros l2; [tauto|]. rewrite IH. tauto.
Qed.

Lemma nr_vals_app : forall l1 l2, nr_vals (l1 ++ l2) <-> nr_vals l1 /\ nr_vals l2.
Proof.
  induction l1 as [|x xs IH]; cbn; intros l2; [tauto|]. rewrite IH. tauto.
Qed.

Lemma nr_exps_map_vval : forall (l : list Val), nr_exps (map VVal l) <-> nr_vals l.
Proof. induction l as [|x xs IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* ----------------------------------------------------------------- *)
(** * Encoding the lexicographic (M1, len_fs, phase) triple as one [nat] *)

(* [(m*(m+1) + l) * 3 + p + 1]: the quadratic term self-scales so that any
   strict decrease in [m] dominates arbitrary changes in [l] (given the
   invariant [l <= m]); the final [*3 + p] breaks ties by phase; the
   trailing [+1] keeps the whole thing strictly positive, so [fuel = 0]
   can never satisfy the bound (needed for the base case of the main
   induction below). *)
Definition encode (m l p : nat) : nat := (m * (m + 1) + l) * 3 + p + 1.

Lemma encode_lt :
  forall m1 l1 p1 m2 l2 p2,
    l1 <= m1 -> l2 <= m2 -> p1 < 3 -> p2 < 3 ->
    (m1 < m2 \/ (m1 = m2 /\ (l1 < l2 \/ (l1 = l2 /\ p1 < p2)))) ->
    encode m1 l1 p1 < encode m2 l2 p2.
Proof.
  intros m1 l1 p1 m2 l2 p2 Hl1 Hl2 Hp1 Hp2 [Hm | [Hm [Hl | [Hl Hp]]]]; unfold encode; nia.
Qed.

Lemma encode_pos : forall m l p, 0 < encode m l p.
Proof. intros. unfold encode. lia. Qed.

Definition Total_exp (e : Exp) (k : FrameStack) : nat := encode (M1_exp e k) (len_fs k) phase_exp.
Definition Total_val (v : Val) (k : FrameStack) : nat := encode (M1_val v k) (len_fs k) phase_val.
Definition Total_il  (e : Exp) (k : FrameStack) : nat := encode (M1_il e k) (len_fs k) phase_il.

Lemma Total_exp_pos : forall e k, 0 < Total_exp e k.
Proof. intros. apply encode_pos. Qed.
Lemma Total_val_pos : forall v k, 0 < Total_val v k.
Proof. intros. apply encode_pos. Qed.
Lemma Total_il_pos : forall e k, 0 < Total_il e k.
Proof. intros. apply encode_pos. Qed.

Lemma len_fs_le_M1_exp : forall e k, len_fs k <= M1_exp e k.
Proof. intros. unfold M1_exp. pose proof (len_fs_le_size_fs k). lia. Qed.

Lemma len_fs_le_M1_val : forall v k, len_fs k <= M1_val v k.
Proof. intros. unfold M1_val. apply len_fs_le_size_fs. Qed.

Lemma len_fs_le_M1_il : forall e k, len_fs k <= M1_il e k.
Proof. intros. unfold M1_il. apply len_fs_le_size_fs. Qed.

Ltac tot_bound := first [apply len_fs_le_M1_exp | apply len_fs_le_M1_val | apply len_fs_le_M1_il].
Ltac tot_phase := unfold phase_exp, phase_val, phase_il; lia.

(* ----------------------------------------------------------------- *)
(** * [Total_*] decrease lemmas, one per machine transition *)

Lemma Total_lt_heat_elet : forall e1 e2 k, Total_exp e1 (FLet e2 :: k) < Total_exp (ELet e1 e2) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply heat_elet]. Qed.

Lemma Total_lt_heat_ecase : forall e0 p e1 e2 k, Total_exp e0 (FCase p e1 e2 :: k) < Total_exp (ECase e0 p e1 e2) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply heat_ecase]. Qed.

Lemma Total_lt_heat_eapp : forall f args k, Total_exp f (FApp1 args :: k) < Total_exp (EApp f args) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply heat_eapp]. Qed.

Lemma Total_lt_heat_ebif : forall f args k, Total_exp f (FBIF1 args :: k) < Total_exp (EBIF f args) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply heat_ebif]. Qed.

Lemma Total_lt_heat_econs : forall e1 e2 k, Total_exp e2 (FCons1 e1 :: k) < Total_exp (ECons e1 e2) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply heat_econs]. Qed.

Lemma Total_lt_let_pop : forall (v:Val) e2 k', Total_exp e2 k' < Total_val v (FLet e2 :: k').
Proof. intros. unfold Total_exp, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply let_pop]. Qed.

Lemma Total_lt_il_let_pop : forall e e2 k', Total_exp e2 k' < Total_il e (FLet e2 :: k').
Proof. intros. unfold Total_exp, Total_il. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply il_let_pop]. Qed.

Lemma Total_lt_case_reduce1 : forall (v:Val) e1 e2 p k', Total_exp e1 k' < Total_val v (FCase p e1 e2 :: k').
Proof. intros. unfold Total_exp, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply (case_reduce v e1 e2 p k')]. Qed.

Lemma Total_lt_case_reduce2 : forall (v:Val) e1 e2 p k', Total_exp e2 k' < Total_val v (FCase p e1 e2 :: k').
Proof. intros. unfold Total_exp, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply (case_reduce v e1 e2 p k')]. Qed.

Lemma Total_lt_vfun_call1 : forall vl body k, Total_exp body [] < Total_exp (VVal (VFun vl body)) k.
Proof. intros. unfold Total_exp. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply (vfun_calls vl body k)]. Qed.

Lemma Total_lt_vfun_call2 : forall vl body k, Total_val (VFun vl body) k < Total_exp (VVal (VFun vl body)) k.
Proof. intros. unfold Total_exp, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply (vfun_calls vl body k)]. Qed.

Lemma Total_lt_fapp1_empty_to_il : forall (v:Val) k', Total_il (EApp (VVal v) []) k' < Total_val v (FApp1 [] :: k').
Proof. intros. unfold Total_il, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply fapp1_empty_to_il]. Qed.

Lemma Total_lt_fapp2_empty_to_il : forall (v f:Val) done k', Total_il (EApp (VVal f) (map VVal done ++ [VVal v])) k' < Total_val v (FApp2 f done [] :: k').
Proof. intros. unfold Total_il, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply fapp2_empty_to_il]. Qed.

Lemma Total_lt_fbif1_empty_to_il : forall (v:Val) k', Total_il (EBIF (VVal v) []) k' < Total_val v (FBIF1 [] :: k').
Proof. intros. unfold Total_il, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply fbif1_empty_to_il]. Qed.

Lemma Total_lt_fbif2_empty_to_il : forall (v f:Val) done k', Total_il (EBIF (VVal f) (map VVal done ++ [VVal v])) k' < Total_val v (FBIF2 f done [] :: k').
Proof. intros. unfold Total_il, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply fbif2_empty_to_il]. Qed.

Lemma Total_lt_fcons2_to_il : forall (v v2:Val) k', Total_il (VVal (VCons v v2)) k' < Total_val v (FCons2 v2 :: k').
Proof. intros. unfold Total_il, Total_val. apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|left; apply fcons2_to_il]. Qed.

Lemma Total_lt_fapp1_to_fapp2 : forall fv f args k',
  Total_exp f (FApp2 fv [] args :: k') < Total_val fv (FApp1 (f :: args) :: k').
Proof.
  intros. unfold Total_exp, Total_val.
  destruct (fapp1_to_fapp2 fv f args k') as [Hle Hlt].
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  assert (M1_exp f (FApp2 fv [] args :: k') < M1_val fv (FApp1 (f :: args) :: k')
          \/ M1_exp f (FApp2 fv [] args :: k') = M1_val fv (FApp1 (f :: args) :: k')) as [Hlt'|Heq] by lia.
  - left; exact Hlt'.
  - right; split; [exact Heq | left; apply Hlt; exact Heq].
Qed.

Lemma Total_lt_fapp2_todo_shift : forall fv prevv done x rest k',
  Total_exp x (FApp2 fv (done ++ [prevv]) rest :: k') < Total_val prevv (FApp2 fv done (x :: rest) :: k').
Proof.
  intros. unfold Total_exp, Total_val.
  destruct (fapp2_todo_shift fv prevv done x rest k') as [Hle Hlt].
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  assert (M1_exp x (FApp2 fv (done ++ [prevv]) rest :: k') < M1_val prevv (FApp2 fv done (x :: rest) :: k')
          \/ M1_exp x (FApp2 fv (done ++ [prevv]) rest :: k') = M1_val prevv (FApp2 fv done (x :: rest) :: k')) as [Hlt'|Heq] by lia.
  - left; exact Hlt'.
  - right; split; [exact Heq | left; apply Hlt; exact Heq].
Qed.

Lemma Total_lt_fcons1_to_fcons2 : forall prevv e1 k',
  Total_exp e1 (FCons2 prevv :: k') < Total_val prevv (FCons1 e1 :: k').
Proof.
  intros. unfold Total_exp, Total_val.
  destruct (fcons1_to_fcons2 prevv e1 k') as [Hle Hlt].
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  assert (M1_exp e1 (FCons2 prevv :: k') < M1_val prevv (FCons1 e1 :: k')
          \/ M1_exp e1 (FCons2 prevv :: k') = M1_val prevv (FCons1 e1 :: k')) as [Hlt'|Heq] by lia.
  - left; exact Hlt'.
  - right; split; [exact Heq | left; apply Hlt; exact Heq].
Qed.

Lemma Total_lt_fbif1_to_fbif2 : forall fv f args k',
  Total_exp f (FBIF2 fv [] args :: k') < Total_val fv (FBIF1 (f :: args) :: k').
Proof.
  intros. unfold Total_exp, Total_val.
  destruct (fbif1_to_fbif2 fv f args k') as [Hle Hlt].
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  assert (M1_exp f (FBIF2 fv [] args :: k') < M1_val fv (FBIF1 (f :: args) :: k')
          \/ M1_exp f (FBIF2 fv [] args :: k') = M1_val fv (FBIF1 (f :: args) :: k')) as [Hlt'|Heq] by lia.
  - left; exact Hlt'.
  - right; split; [exact Heq | left; apply Hlt; exact Heq].
Qed.

Lemma Total_lt_fbif2_todo_shift : forall fv prevv done x rest k',
  Total_exp x (FBIF2 fv (done ++ [prevv]) rest :: k') < Total_val prevv (FBIF2 fv done (x :: rest) :: k').
Proof.
  intros. unfold Total_exp, Total_val.
  destruct (fbif2_todo_shift fv prevv done x rest k') as [Hle Hlt].
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  assert (M1_exp x (FBIF2 fv (done ++ [prevv]) rest :: k') < M1_val prevv (FBIF2 fv done (x :: rest) :: k')
          \/ M1_exp x (FBIF2 fv (done ++ [prevv]) rest :: k') = M1_val prevv (FBIF2 fv done (x :: rest) :: k')) as [Hlt'|Heq] by lia.
  - left; exact Hlt'.
  - right; split; [exact Heq | left; apply Hlt; exact Heq].
Qed.

Lemma Total_lt_vval_delegate : forall (v : Val) (k : FrameStack),
  (match v with VFun _ _ => False | _ => True end) ->
  Total_val v k < Total_exp (VVal v) k.
Proof.
  intros v k Hnf.
  destruct (vval_delegate v k Hnf) as [Hle Hlt].
  assert (Heq : M1_exp (VVal v) k = M1_val v k).
  { unfold M1_exp, M1_val, focus_weight in *. destruct v; try contradiction; lia. }
  unfold Total_exp, Total_val.
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  right. split; [symmetry; exact Heq | right; split; [reflexivity | apply Hlt; exact Heq]].
Qed.

Lemma Total_lt_il_is_value_handoff : forall (e_arg : Exp) (k : FrameStack),
  (match e_arg with VVal (VFun _ _) => False | VVal _ => True | _ => False end) ->
  Total_exp e_arg k < Total_il e_arg k.
Proof.
  intros e_arg k Hval.
  destruct (il_is_value_handoff e_arg k Hval) as [Hle Hlt].
  assert (Heq : M1_exp e_arg k = M1_il e_arg k).
  { unfold M1_exp, M1_il, focus_weight in *. destruct e_arg as [nv|v]; [contradiction|].
    destruct v; try contradiction; lia. }
  unfold Total_exp, Total_il.
  apply encode_lt; [tot_bound|tot_bound|tot_phase|tot_phase|].
  right. split; [exact Heq | right; split; [reflexivity | apply Hlt; exact Heq]].
Qed.

Lemma Total_exp_rename_framestack : forall e k r, Total_exp e (rename_framestack r k) = Total_exp e k.
Proof. intros e k r. unfold Total_exp, M1_exp. now rewrite size_fs_rename, len_fs_rename. Qed.

Lemma Total_il_indep : forall e1 e2 k, Total_il e1 k = Total_il e2 k.
Proof. reflexivity. Qed.

Lemma Total_lt_il_rename : forall (e : Exp) (k : FrameStack),
  Total_exp (VVar 0) (rename_framestack S k) < Total_il e k.
Proof.
  intros e k.
  rewrite Total_exp_rename_framestack, (Total_il_indep e (VVar 0) k).
  apply (Total_lt_il_is_value_handoff (VVar 0) k I).
Qed.

(* ----------------------------------------------------------------- *)
(** * [introduce_let] is total given a sufficiently-fueled [normalize_exp] *)

Lemma introduce_let_nonlet_step :
  forall (f : Exp -> FrameStack -> option Exp) (fr : Frame) (k' : FrameStack) (e : Exp) (n : nat),
    (match e with VVal (VFun _ _) => False | _ => True end) ->
    (forall e' k'0, no_receive_exp e' -> no_receive_fs k'0 -> Total_exp e' k'0 <= n ->
       exists res, f e' k'0 = Some res /\ no_receive_exp res) ->
    no_receive_exp e -> no_receive_fs (fr :: k') ->
    Total_il e (fr :: k') <= S n ->
    exists res,
      (if is_value e then f e (fr :: k')
       else fmap (fun e' => EExp (ELet e e'))
              (f (VVar 0) (rename_framestack (fun n => S n) (fr :: k'))))
      = Some res /\ no_receive_exp res.
Proof.
  intros f fr k' e n Hnotfun IH He Hk Hbound.
  replace (fun n : nat => S n) with S by reflexivity.
  destruct (is_value e) eqn:Eisval.
  - assert (Hval : match e with VVal (VFun _ _) => False | VVal _ => True | _ => False end).
    { destruct e as [nv|v]; cbn in Eisval; try discriminate. destruct v; auto. }
    apply IH; auto.
    pose proof (Total_lt_il_is_value_handoff e (fr :: k') Hval) as Hlt.
    lia.
  - destruct (IH (VVar 0) (rename_framestack S (fr::k'))) as [res [Hres Hnr]].
    + exact I.
    + now apply no_receive_fs_rename.
    + pose proof (Total_lt_il_rename e (fr :: k')) as Hlt. lia.
    + rewrite Hres. cbn. eexists. split; [reflexivity|]. cbn. auto.
Qed.

Lemma introduce_let_total :
  forall (f : Exp -> FrameStack -> option Exp) (k : FrameStack) (e : Exp) (n : nat),
    (match e with VVal (VFun _ _) => False | _ => True end) ->
    (forall e' k', no_receive_exp e' -> no_receive_fs k' -> Total_exp e' k' <= n ->
       exists res, f e' k' = Some res /\ no_receive_exp res) ->
    no_receive_exp e -> no_receive_fs k ->
    Total_il e k <= S n ->
    exists res, introduce_let f k e = Some res /\ no_receive_exp res.
Proof.
  intros f k e n Hnotfun IH He Hk Hbound.
  unfold introduce_let.
  destruct k as [|fr k'].
  - exists e. split; [reflexivity | exact He].
  - destruct fr eqn:Efr; subst;
      try (apply (introduce_let_nonlet_step f _ k' e n); auto; exact Hbound).
    (* remaining case: fr = FLet e2 *)
    cbn in Hk. destruct Hk as [He2 Hk'].
    destruct (IH e2 k') as [res [Hres Hnr]].
    + assumption.
    + assumption.
    + pose proof (Total_lt_il_let_pop e e2 k') as Hlt. lia.
    + rewrite Hres. cbn. eexists. split; [reflexivity|]. cbn. auto.
Qed.

(* ----------------------------------------------------------------- *)
(** * Main theorem *)

Lemma normalize_total_helper :
  forall fuel,
    (forall e k, no_receive_exp e -> no_receive_fs k -> Total_exp e k <= fuel ->
       exists res, normalize_exp fuel e k = Some res /\ no_receive_exp res) /\
    (forall v k, no_receive_val v -> no_receive_fs k -> Total_val v k <= fuel ->
       exists res, normalize_val fuel v k = Some res /\ no_receive_exp res).
Proof.
  induction fuel as [|fuel' [IHexp IHval]].
  - split.
    + intros e k _ _ Hbound. pose proof (Total_exp_pos e k). lia.
    + intros v k _ _ Hbound. pose proof (Total_val_pos v k). lia.
  - split.
    + intros e k Hre Hrk Hbound.
      destruct e as [nv | v].
      * destruct nv as [exp l|e1 e2|e0 p e1 e2|e1 e2|cases|exp l].
        -- (* EApp *)
           cbn [normalize_exp].
           cbn in Hre. apply no_receive_app_iff in Hre. destruct Hre as [Hre1 Hre2].
           apply IHexp; [exact Hre1 | cbn; split; assumption | ].
           pose proof (Total_lt_heat_eapp exp l k). lia.
        -- (* ELet *)
           cbn [normalize_exp].
           cbn in Hre. destruct Hre as [Hre1 Hre2].
           apply IHexp; [exact Hre1 | cbn; split; assumption | ].
           pose proof (Total_lt_heat_elet e1 e2 k). lia.
        -- (* ECase *)
           cbn [normalize_exp].
           cbn in Hre. destruct Hre as [Hre0 [Hre1 Hre2]].
           apply IHexp; [exact Hre0 | cbn; auto | ].
           pose proof (Total_lt_heat_ecase e0 p e1 e2 k). lia.
        -- (* ECons *)
           cbn [normalize_exp].
           cbn in Hre. destruct Hre as [Hre1 Hre2].
           apply IHexp; [exact Hre2 | cbn; split; assumption | ].
           pose proof (Total_lt_heat_econs e1 e2 k). lia.
        -- (* EReceive: vacuous, ruled out by hypothesis *)
           cbn in Hre. contradiction.
        -- (* EBIF *)
           cbn [normalize_exp].
           cbn in Hre. apply no_receive_bif_iff in Hre. destruct Hre as [Hre1 Hre2].
           apply IHexp; [exact Hre1 | cbn; split; assumption | ].
           pose proof (Total_lt_heat_ebif exp l k). lia.
      * destruct v as [lit|pid|nv|vl body|  |v1 v2].
        -- cbn [normalize_exp]. apply IHval; [exact Hre | exact Hrk | ].
           pose proof (Total_lt_vval_delegate (VLit lit) k I). lia.
        -- cbn [normalize_exp]. apply IHval; [exact Hre | exact Hrk | ].
           pose proof (Total_lt_vval_delegate (VPid pid) k I). lia.
        -- cbn [normalize_exp]. apply IHval; [exact Hre | exact Hrk | ].
           pose proof (Total_lt_vval_delegate (VVar nv) k I). lia.
        -- (* VFun: two internal calls sharing one fuel level *)
           cbn [normalize_exp].
           cbn in Hre.
           assert (Hb1 : Total_exp body [] <= fuel')
             by (pose proof (Total_lt_vfun_call1 vl body k); lia).
           destruct (IHexp body [] Hre I Hb1) as [body' [Hbody' Hnrbody']].
           unfold mbind. rewrite Hbody'. cbn.
           assert (Hb2 : Total_val (VFun vl body') k <= fuel')
             by (pose proof (Total_lt_vfun_call2 vl body k); unfold Total_val, M1_val in *; lia).
           apply IHval; [exact Hnrbody' | exact Hrk | exact Hb2].
        -- cbn [normalize_exp]. apply IHval; [exact Hre | exact Hrk | ].
           pose proof (Total_lt_vval_delegate VNil k I). lia.
        -- cbn [normalize_exp]. apply IHval; [exact Hre | exact Hrk | ].
           pose proof (Total_lt_vval_delegate (VCons v1 v2) k I). lia.
    + intros v k Hrv Hrk Hbound.
      destruct k as [|fr k'].
      * cbn [normalize_val]. exists (VVal v). split; [reflexivity | exact Hrv].
      * destruct fr as [args|fv done todo|e2|p e1 e2|e1|v2|args|fv done todo].
        -- (* FApp1 *) destruct args as [|f args'].
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [Hrargs Hrk'].
              apply (introduce_let_total (normalize_exp fuel') k' (EApp (VVal v) []) fuel' I IHexp).
              ** apply no_receive_app_iff. split; [exact Hrv | exact I].
              ** exact Hrk'.
              ** pose proof (Total_lt_fapp1_empty_to_il v k'). lia.
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrf Hrargs'] Hrk'].
              apply IHexp; [exact Hrf | cbn; repeat split; auto | ].
              pose proof (Total_lt_fapp1_to_fapp2 v f args' k'). lia.
        -- (* FApp2 *) destruct todo as [|fe todo'].
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrfv [Hrdone Hrtodo]] Hrk'].
              apply (introduce_let_total (normalize_exp fuel') k' (EApp (VVal fv) (map VVal done ++ [VVal v])) fuel' I IHexp).
              ** apply no_receive_app_iff. split; [exact Hrfv | ].
                 apply nr_exps_app. split; [now apply nr_exps_map_vval | cbn; auto].
              ** exact Hrk'.
              ** pose proof (Total_lt_fapp2_empty_to_il v fv done k'). lia.
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrfv [Hrdone [Hrfe Hrtodo']]] Hrk'].
              assert (Hnrf : no_receive_fs (FApp2 fv (done ++ [v]) todo' :: k')).
              { cbn. repeat split; auto. apply nr_vals_app. split; [exact Hrdone | cbn; auto]. }
              apply IHexp; [exact Hrfe | exact Hnrf | ].
              pose proof (Total_lt_fapp2_todo_shift fv v done fe todo' k'). lia.
        -- (* FLet *) cbn [normalize_val]. cbn in Hrk. destruct Hrk as [Hre2 Hrk'].
           assert (Hb : Total_exp e2 k' <= fuel')
             by (pose proof (Total_lt_let_pop v e2 k'); lia).
           destruct (IHexp e2 k' Hre2 Hrk' Hb) as [res [Hres Hnr]].
           rewrite Hres. cbn. eexists. split; [reflexivity|]. cbn. auto.
        -- (* FCase *) cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hre1 Hre2] Hrk'].
           assert (Hb1 : Total_exp e1 k' <= fuel')
             by (pose proof (Total_lt_case_reduce1 v e1 e2 p k'); lia).
           destruct (IHexp e1 k' Hre1 Hrk' Hb1) as [res1 [Hres1 Hnr1]].
           assert (Hb2 : Total_exp e2 k' <= fuel')
             by (pose proof (Total_lt_case_reduce2 v e1 e2 p k'); lia).
           destruct (IHexp e2 k' Hre2 Hrk' Hb2) as [res2 [Hres2 Hnr2]].
           unfold mbind. rewrite Hres1. cbn. rewrite Hres2. cbn.
           eexists. split; [reflexivity|]. cbn. auto.
        -- (* FCons1 *) cbn [normalize_val]. cbn in Hrk. destruct Hrk as [Hre1 Hrk'].
           apply IHexp; [exact Hre1 | cbn; auto | ].
           pose proof (Total_lt_fcons1_to_fcons2 v e1 k'). lia.
        -- (* FCons2 *) cbn [normalize_val]. cbn in Hrk. destruct Hrk as [Hrv2 Hrk'].
           apply (introduce_let_total (normalize_exp fuel') k' (VVal (VCons v v2)) fuel' I IHexp).
           ++ cbn; auto.
           ++ exact Hrk'.
           ++ pose proof (Total_lt_fcons2_to_il v v2 k'). lia.
        -- (* FBIF1 *) destruct args as [|f args'].
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [Hrargs Hrk'].
              apply (introduce_let_total (normalize_exp fuel') k' (EBIF (VVal v) []) fuel' I IHexp).
              ** apply no_receive_bif_iff. split; [exact Hrv | exact I].
              ** exact Hrk'.
              ** pose proof (Total_lt_fbif1_empty_to_il v k'). lia.
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrf Hrargs'] Hrk'].
              apply IHexp; [exact Hrf | cbn; repeat split; auto | ].
              pose proof (Total_lt_fbif1_to_fbif2 v f args' k'). lia.
        -- (* FBIF2 *) destruct todo as [|fe todo'].
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrfv [Hrdone Hrtodo]] Hrk'].
              apply (introduce_let_total (normalize_exp fuel') k' (EBIF (VVal fv) (map VVal done ++ [VVal v])) fuel' I IHexp).
              ** apply no_receive_bif_iff. split; [exact Hrfv | ].
                 apply nr_exps_app. split; [now apply nr_exps_map_vval | cbn; auto].
              ** exact Hrk'.
              ** pose proof (Total_lt_fbif2_empty_to_il v fv done k'). lia.
           ++ cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hrfv [Hrdone [Hrfe Hrtodo']]] Hrk'].
              assert (Hnrf : no_receive_fs (FBIF2 fv (done ++ [v]) todo' :: k')).
              { cbn. repeat split; auto. apply nr_vals_app. split; [exact Hrdone | cbn; auto]. }
              apply IHexp; [exact Hrfe | exact Hnrf | ].
              pose proof (Total_lt_fbif2_todo_shift fv v done fe todo' k'). lia.
Qed.

Corollary normalize_exp_total :
  forall e, no_receive_exp e ->
    exists res, normalize_exp (Total_exp e []) e [] = Some res /\ no_receive_exp res.
Proof.
  intros e He.
  destruct (normalize_total_helper (Total_exp e [])) as [Hexp _].
  apply Hexp; [exact He | exact I | lia].
Qed.

Corollary normalize_exp_terminates :
  forall e, no_receive_exp e -> exists fuel res, normalize_exp fuel e [] = Some res.
Proof.
  intros e He.
  destruct (normalize_exp_total e He) as [res [Hres _]].
  eauto.
Qed.

































From CoreErlang.Subst Require Export Compatibility.

Corollary CIU_open_refl :
  forall Γ e, EXP Γ ⊢ e -> CIU_open Γ e e.
Proof.
  intros. apply Erel_implies_CIU.
  by apply Erel_Fundamental.
Qed.


Lemma normalize_preserves_semantics fuel : forall Γ k e anf,
  EXP Γ ⊢ plug_fs k e ->
  normalize_exp fuel e k = Some anf ->
  CIU_open Γ (plug_fs k e) anf.
Proof.
  induction fuel using lt_wf_ind. rename H into IHfuel.
  destruct fuel; intros * (* Hpre *) D H; simpl in H. congruence.
  destruct e; simpl in H; try congruence.
  * destruct e; simpl in H; try congruence.
    all: eapply IHfuel in H; [ simpl in H; eassumption | lia | by simpl ].
  * destruct v; simpl in *; try congruence.
    all: destruct fuel; simpl in *; try congruence.
    - destruct k. 2: destruct f. all: simpl in *.
      + inv H. simpl. apply CIU_open_refl. repeat constructor.
      + destruct l0.
        ** unfold introduce_let in H; destruct k; simpl in *; inv H.
           1: by apply CIU_open_refl.
           destruct f; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           all: eapply IHfuel in Hexp; try lia; cbn in *.
           -- 
           
        ** eapply IHfuel in H; [ simpl in H; eassumption | lia | by simpl ].
      +
      +
      +
      +
      +
      +
      +
    -
    -
    -
    -
    -
Qed.






(* NOTE:
   This version won't hold, even though, it shows promising progress. The issue
   is with i) scoping and ii) closures.

   i) introduce_let is used inside a let expression, and therefore, the scope
      of the normalisation is 1 + (the scope of the original expression). This
      scope extension is not expressed in the statement.
   ii) the syntax of closures get altered---the closure body is adjusted to be
      in ANF form. Therefore, the final results (if they are closures) could
      not be proven equal. This could be avoided by the use of CIU.

 *)
Lemma normalize_preserves_semantics fuel : forall k e anf v,
  ⟨k, e⟩ -->* v ->
  normalize_exp fuel e k = Some anf ->
  ⟨[], anf⟩ -->* v.
Proof.
  (* induction fuel using lt_wf_ind. rename H into IHfuel.
  destruct fuel; intros * (* Hpre *) D H; simpl in H. congruence.
  destruct e; simpl in H; try congruence.
  * destruct e; simpl in H; try congruence.
    - eapply IHfuel in H. eassumption. lia.
      inv D. inv H0. inv H1.
      by eexists.
    - eapply IHfuel in H. eassumption. lia.
      inv D. inv H0. inv H1.
      by eexists.
    - eapply IHfuel in H. eassumption. lia.
      inv D. inv H0. inv H1.
      by eexists.
    - eapply IHfuel in H. eassumption. lia.
      inv D. inv H0. inv H1.
      by eexists.
    - eapply IHfuel in H. eassumption. lia.
      inv D. inv H0. inv H1.
      by eexists.
  * destruct v0; simpl in H; try congruence.
    (* The following technique is repeated for almost all values: ("-" bullets) *)
    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. assumption.
      + destruct l0.
        ** unfold introduce_let in H.
           destruct k.
           1: { inv H. inv D. eexists. econstructor. constructor. eassumption. }
           destruct f; simpl in *.
           all: destruct normalize_exp eqn:Hexp in H; simpl in H.
           
           
            inv H.
           -- destruct fuel; simpl in *; try congruence.
              destruct fuel; simpl in *; try congruence.
        ** eapply IHfuel in H. eassumption. lia.
           inv D. inv H0. inv H1.
           by eexists.
      +
      +
      +
      +
      +
      +
      +
    -
    -
    -
    -
    - *)
Abort.
