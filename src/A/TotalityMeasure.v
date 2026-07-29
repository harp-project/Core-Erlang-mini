From CoreErlang.A Require Import Syntax.

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
    destruct (IH e2 (rename_framestack (fun n => S n) k')) as [res [Hres Hnr]].
    + assumption.
    + now apply no_receive_fs_rename.
    + rewrite Total_exp_rename_framestack.
      pose proof (Total_lt_il_let_pop e e2 k') as Hlt. lia.
    + simpl. rewrite Hres. cbn. eexists. split; [reflexivity|]. cbn. auto.
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
           unfold mbind. simpl. rewrite Hbody'. cbn.
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
           assert (Hrk'' : no_receive_fs (rename_framestack (fun n => S n) k'))
             by (now apply no_receive_fs_rename).
           assert (Hb : Total_exp e2 (rename_framestack (fun n => S n) k') <= fuel')
             by (rewrite Total_exp_rename_framestack; pose proof (Total_lt_let_pop v e2 k'); lia).
           destruct (IHexp e2 (rename_framestack (fun n => S n) k') Hre2 Hrk'' Hb) as [res [Hres Hnr]].
           rewrite Hres. cbn. eexists. split; [reflexivity|]. cbn. auto.
        -- (* FCase *) cbn [normalize_val]. cbn in Hrk. destruct Hrk as [[Hre1 Hre2] Hrk'].
           assert (Hrk1'' : no_receive_fs (rename_framestack (fun n => pat_vars p + n) k'))
             by (now apply no_receive_fs_rename).
           assert (Hb1 : Total_exp e1 (rename_framestack (fun n => pat_vars p + n) k') <= fuel')
             by (rewrite Total_exp_rename_framestack; pose proof (Total_lt_case_reduce1 v e1 e2 p k'); lia).
           destruct (IHexp e1 (rename_framestack (fun n => pat_vars p + n) k') Hre1 Hrk1'' Hb1) as [res1 [Hres1 Hnr1]].
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

(** ----------------------------------------------------------------- *)
(** * [introduce_let]'s renamed-continuation congruence

  [introduce_let]'s wildcard (non-[FLet]) branch wraps a fresh [ELet e0 ...]
  around the current (non-atomic) redex [e0], and continues normalizing
  [VVar 0] against the *whole* continuation shifted by one
  ([rename_framestack (fun n => S n)]). The lemmas below show that this
  shift is exactly undone by substituting the fresh binder's value back in,
  which is what lets [introduce_let_CIU_cong] connect [Hexp] (about the
  shifted/renamed continuation) back to the un-renamed goal, via CIU's
  frame-based semantics ([put_back]/[put_back_fs]/[term_eval_both]).
  [introduce_let_CIU_cong] and [introduce_let_side_scope] are stated
  generically over the frame [f0] being processed, and close EVERY
  non-[FLet] "--" case below identically (verified for [FApp1] and
  [FApp2]; the same two-line pattern applies unchanged to [FCase],
  [FCons1], [FCons2], [FBIF1], [FBIF2]).
*)

Lemma rename_subst_core_frame : forall f v ξ,
  (rename_frame (fun n => S n) f).ₜ[v .: ξ] = f.ₜ[ξ].
Proof.
  destruct f; intros; cbn.
  - f_equal. apply rename_subst_list.
  - rewrite rename_subst_core_val. f_equal.
    apply rename_subst_list_val.
    apply rename_subst_list.
  - f_equal.
    rewrite renaming_is_subst, subst_ren, upren_subst_up.
    assert (Hcomp : (fun n : nat => S n) >>> (v .: ξ) = ξ) by (extensionality n; reflexivity).
    rewrite Hcomp. reflexivity.
  - f_equal.
    + rewrite renaming_is_subst, subst_ren, uprenn_subst_upn.
      assert (Hcomp : (fun n : nat => S n) >>> (v .: ξ) = ξ) by (extensionality n; reflexivity).
      rewrite Hcomp. reflexivity.
    + apply rename_subst_core.
  - f_equal. apply rename_subst_core.
  - f_equal. apply rename_subst_core_val.
  - f_equal. apply rename_subst_list.
  - rewrite rename_subst_core_val. f_equal.
    apply rename_subst_list_val.
    apply rename_subst_list.
Qed.

Lemma rename_subst_core_framestack : forall k v ξ,
  (rename_framestack (fun n => S n) k).ₖ[v .: ξ] = k.ₖ[ξ].
Proof.
  induction k as [|f k IH]; intros; cbn; auto.
  unfold rename_framestack, subst_framestack in *. cbn.
  rewrite rename_subst_core_frame, IH. reflexivity.
Qed.

Lemma rename_frame_id f :
  rename_frame id f = f.
Proof.
  destruct f; simpl;
    try (f_equal; rewrite <- map_id at 2; apply map_ext; intros; apply idrenaming_is_id).
  1: { f_equal.
       transitivity (map id l).
       apply map_ext, idrenaming_is_id.
       apply map_id. }
  rewrite idrenaming_is_id_val.
  f_equal.
  transitivity (map id l1).
  apply map_ext, idrenaming_is_id_val.
  apply map_id.
  transitivity (map id l2).
  apply map_ext, idrenaming_is_id.
  apply map_id.
  rewrite idrenaming_up, idrenaming_is_id.
  reflexivity.
  rewrite idrenaming_upn, idrenaming_is_id, idrenaming_is_id.
  reflexivity.
  rewrite idrenaming_is_id.
  reflexivity.
  rewrite idrenaming_is_id_val.
  reflexivity.
  f_equal.
  transitivity (map id l).
  apply map_ext, idrenaming_is_id.
  apply map_id.
  rewrite idrenaming_is_id_val.
  f_equal.
  transitivity (map id l1).
  apply map_ext, idrenaming_is_id_val.
  apply map_id.
  transitivity (map id l2).
  apply map_ext, idrenaming_is_id.
  apply map_id.
Qed.

Lemma rename_framestack_id k :
  rename_framestack id k = k.
Proof.
  unfold rename_framestack.
  transitivity (map id k).
  apply map_ext, rename_frame_id.
  apply map_id.
Qed.

Lemma rename_subst_core_framestack_list_subst : forall k l ξ m,
  m = length l ->
  (rename_framestack (fun n => m + n) k).ₖ[list_subst l ξ] = k.ₖ[ξ].
Proof.
  induction l; simpl; intros; subst.
  { replace (fun n : nat => 0 + n) with (@id nat) by (extensionality n; reflexivity).
    rewrite rename_framestack_id.
    reflexivity. }
  specialize (IHl ξ (length l) eq_refl).
  rewrite <- IHl.
  rewrite <- rename_subst_core_framestack with (v := a) (k := (rename_framestack (λ n : nat, base.length l + n) k)).
  f_equal.
  unfold rename_framestack.
  rewrite map_map.
  f_equal. f_equal. clear.
  extensionality f. destruct f; simpl; repeat rewrite map_map.
  { f_equal.
    apply map_ext. intros x. rewrite rename_comp. f_equal. }
  { f_equal.
    rewrite rename_comp_val. f_equal.
    apply map_ext. intros x. rewrite rename_comp_val. f_equal.
    apply map_ext. intros x. rewrite rename_comp. f_equal. }
  { f_equal.
    rewrite rename_comp, upren_comp. f_equal. }
  f_equal.
  rewrite rename_comp, uprenn_comp. f_equal.
  rewrite rename_comp. f_equal.
  f_equal. rewrite rename_comp. f_equal.
  f_equal. rewrite rename_comp_val. f_equal.
  f_equal.
  apply map_ext. intros x. rewrite rename_comp. f_equal.
  f_equal.
  rewrite rename_comp_val. f_equal.
  apply map_ext. intros x. rewrite rename_comp_val. f_equal.
  apply map_ext. intros x. rewrite rename_comp. f_equal.
Qed.

Lemma plug_f_rename_subst_core : forall f0 v ξ,
  (plug_f (rename_frame (fun n => S n) f0) (˝ VVar 0)).[v .: ξ] = plug_f (f0.ₜ[ξ]) (˝ v).
Proof.
  intros. rewrite plug_f_subst, rename_subst_core_frame. reflexivity.
Qed.

Lemma plug_fs_rename_subst_core : forall k v ξ,
  (plug_fs (rename_framestack (fun n => S n) k) (˝ VVar 0)).[v .: ξ]
  = plug_fs (k.ₖ[ξ]) (˝ v).
Proof.
  intros. rewrite plug_fs_subst, rename_subst_core_framestack. reflexivity.
Qed.

(** ["A rename by [f0's] own binder-lifting is undone by weakening"]:
    scope side of the same story, needed for [introduce_let]'s recursive
    call's own premise (that the renamed continuation is well-scoped). *)

Lemma plug_f_hole_scope : forall f Γ e1 e2,
  EXP Γ ⊢ plug_f f e1 -> EXP Γ ⊢ e2 -> EXP Γ ⊢ plug_f f e2.
Proof.
  intros f Γ e1 e2 He1 He2.
  destruct f; cbn in *; inv He1; try constructor; auto.
  all: inv H0; constructor; auto.
  all: intros i Hi; destruct (Nat.eq_dec i (base.length (map VVal l1))) as [Heq|Hneq].
  1,3: subst; rewrite app_nth2 by lia; rewrite Nat.sub_diag; cbn; auto.
  all: assert (Hi' : i < base.length (map VVal l1 ++ e1 :: l2)) by (rewrite length_app in *; cbn in *; lia);
       specialize (H3 i Hi'); revert H3;
       destruct (Nat.lt_ge_cases i (base.length (map VVal l1))) as [Hlt|Hge].
  all: intros H3''.
  1,3: rewrite !app_nth1 in *; try (rewrite ?length_map; lia); auto.
  1,2: rewrite !app_nth2 in *; try (rewrite ?length_map; lia);
       replace (i - base.length (map VVal l1)) with (S (i - base.length (map VVal l1) - 1)) in * by lia; cbn in *; auto.
Qed.

Lemma plug_f_extract_hole_scope : forall f Γ e, EXP Γ ⊢ plug_f f e -> EXP Γ ⊢ e.
Proof.
  intros f Γ e He.
  destruct f; cbn in *; inv He; inv H0; auto.
  all: specialize (H3 (base.length (map VVal l1)));
       rewrite length_app in H3; cbn in H3; rewrite length_map in H3;
       specialize (H3 ltac:(lia));
       rewrite app_nth2 in H3 by (rewrite length_map; lia);
       rewrite length_map, Nat.sub_diag in H3; exact H3.
Qed.

Lemma plug_fs_extract_hole_scope : forall k Γ e, EXP Γ ⊢ plug_fs k e -> EXP Γ ⊢ e.
Proof.
  induction k as [|f k IH]; intros Γ e He; cbn in *.
  - exact He.
  - apply plug_f_extract_hole_scope with f. eapply IH. exact He.
Qed.

Lemma plug_fs_hole_scope : forall k Γ e1 e2,
  EXP Γ ⊢ plug_fs k e1 -> EXP Γ ⊢ e2 -> EXP Γ ⊢ plug_fs k e2.
Proof.
  induction k as [|f k IH]; intros Γ e1 e2 Hke1 He2; cbn in *.
  - exact He2.
  - apply IH with (e1 := plug_f f e1).
    + exact Hke1.
    + apply plug_f_hole_scope with e1; auto.
      eapply plug_fs_extract_hole_scope; exact Hke1.
Qed.

Lemma shift_renscope : forall Γ m, RENSCOPE Γ ⊢ (fun n => m + n) ∷ (m + Γ).
Proof. intros Γ n m Hn. cbn. lia. Qed.

Lemma rename_scope_add : forall Γ m e, EXP Γ ⊢ e -> EXP (m + Γ) ⊢ rename (fun n => m + n) e.
Proof.
  intros.
  apply -> ren_preserves_scope; try eassumption.
  apply shift_renscope.
Qed.



Lemma plug_f_rename : forall f e ρ, plug_f (rename_frame ρ f) (rename ρ e) = rename ρ (plug_f f e).
Proof.
  destruct f; intros; cbn; try reflexivity.
  - rewrite map_app, map_map. simpl. rewrite map_map. reflexivity.
  - rewrite map_app, map_map. simpl. rewrite map_map. reflexivity.
Qed.

Lemma plug_fs_rename : forall k e ρ, plug_fs (rename_framestack ρ k) (rename ρ e) = rename ρ (plug_fs k e).
Proof.
  induction k as [|f k IH]; intros; cbn; auto.
  unfold rename_framestack in *. cbn. rewrite plug_f_rename. apply IH.
Qed.

(** The scope side-condition [introduce_let]'s recursive call needs:
    the renamed continuation, with a fresh [VVar 0] plugged into the hole
    left by [f0], is well-scoped one level up. *)
Lemma introduce_let_side_scope : forall Γ k e0,
  EXP Γ ⊢ plug_fs k e0 ->
  EXP (S Γ) ⊢ plug_fs (rename_framestack (fun n => S n) k) (˝ VVar 0).
Proof.
  intros Γ k e0 D.
  pose proof (rename_scope_add Γ 1 (plug_fs k e0) D) as H1.
  rewrite <- plug_fs_rename in H1.
  eapply plug_fs_hole_scope. exact H1.
  constructor. constructor. lia.
Qed.

(** The main congruence: [introduce_let]'s "wrap the redex in a fresh let,
    continue with the shifted continuation" step preserves CIU. Generic in
    [f0] -- covers every non-[FLet] frame constructor identically. *)
Lemma introduce_let_CIU_cong : forall Γ k e0 e,
  EXP Γ ⊢ plug_fs k e0 ->
  CIU_open (S Γ) (plug_fs (rename_framestack (fun n => S n) k) (˝ VVar 0)) e ->
  CIU_open Γ (plug_fs k e0) (° ELet e0 e).
Proof.
  intros Γ k e0 e D Hexp ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (plug_fs k e0).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  assert (He : EXP (S Γ) ⊢ e) by (eapply CIU_open_scope_r; eauto).
  assert (Hclosed2 : EXPCLOSED (° ELet e0 e).[ξ]). {
    apply -> subst_preserves_scope_exp. 2: eassumption.
    do 2 constructor; eauto.
    by apply plug_fs_extract_hole_scope in D.
  }
  assert (Hclosed_e0 : EXPCLOSED e0.[ξ]). {
    apply -> subst_preserves_scope_exp; eauto.
    by apply plug_fs_extract_hole_scope in D.
  }
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  rewrite plug_fs_subst in HT.
  apply put_back_rev_fs in HT.
  destruct HT as [x HT2].
  pose proof (term_eval_both x (k.ₖ[ξ] ++ F) (e0.[ξ]) HT2) as [v0 [j [D1 D2]]].
  assert (Hv0cl : VALCLOSED v0)
    by (eapply step_any_closedness; [exists j; exact D1 | constructor | exact Hclosed_e0]).
  pose proof (terminates_step_any_2 j x _ _ HT2 _ _ D2) as HT3.

  apply ex_intro with (x := x - j) in HT3.
  eapply put_back_fs in HT3. rewrite <- plug_fs_rename_subst_core in HT3.
  assert (Hscope0 : SUBSCOPE (S Γ) ⊢ v0 .: ξ ∷ 0) by (apply cons_scope; auto).
  pose proof (Hexp (v0 .: ξ) Hscope0) as [_ [_ Hcont]].
  specialize (Hcont F HF HT3) as [limit DD].
  eexists. simpl.
  constructor. eapply term_step_term_plus.
  eapply frame_indep_core in D1. exact D1.
  simpl. constructor.
  rewrite subst_comp, subst_extend_id. eassumption.
Qed.


(** [FLet]'s own branch (in both [normalize_val] and [introduce_let]) is
    NOT an instance of [introduce_let_CIU_cong]/[introduce_let_side_scope]:
    it reuses the existing let body [e2] directly under the shifted
    continuation, rather than synthesizing a fresh [ELet _ (VVar 0)]. Same
    operational proof technique (pop the [FLet] frame, undo the shift via
    [v0 .: ξ]), just without the extra "wrap in a fresh let" indirection. *)
Lemma plug_fs_CIU_let_compat : forall Γ k e0 e2 e,
  EXP Γ ⊢ plug_fs k (° ELet e0 e2) ->
  CIU_open (S Γ) (plug_fs (rename_framestack (fun n => S n) k) e2) e ->
  CIU_open Γ (plug_fs k (° ELet e0 e2)) (° ELet e0 e).
Proof.
  intros Γ k e0 e2 e D Hexp ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (plug_fs k (° ELet e0 e2)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  assert (He : EXP (S Γ) ⊢ e) by (eapply CIU_open_scope_r; eauto).
  assert (Hclosed2 : EXPCLOSED (° ELet e0 e).[ξ]). {
    apply -> subst_preserves_scope_exp. 2: eassumption.
    apply plug_fs_extract_hole_scope in D. repeat destruct_scope.
    by do 2 constructor.
  }
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  rewrite plug_fs_subst in HT.
  apply put_back_rev_fs in HT.
  destruct HT as [x HT2].
  inv HT2; subst.
  pose proof (term_eval_both k0 ((FLet (e2.[up_subst ξ]) :: k.ₖ[ξ]) ++ F) (e0.[ξ]) H3) as [v0 [j [D1 D2]]].
  pose proof (terminates_step_any_2 j k0 _ _ H3 _ _ D2) as HT3.
  inv HT3.
  apply ex_intro with (x := k1) in H0.
  apply put_back_fs in H0.
  
  assert (Hscope0 : SUBSCOPE (S Γ) ⊢ v0 .: ξ ∷ 0). {
    apply cons_scope; auto.
    apply ex_intro with (x := j) in D1.
    apply step_any_closedness in D1. assumption. constructor.
    inv Hclosed2. inv H1. assumption.
  }
  pose proof (Hexp (v0 .: ξ) Hscope0) as [_ [_ Hcont]].
  specialize (Hcont F HF).
  rewrite plug_fs_subst, rename_subst_core_framestack in Hcont.
  rewrite subst_comp, subst_extend_id in H0.
  specialize (Hcont H0) as [limit DD]. 

  eexists. simpl.
  constructor. eapply term_step_term_plus.
  eapply frame_indep_core in D1. exact D1.
  simpl. constructor.
  rewrite subst_comp, subst_extend_id. eassumption.
Qed.

Lemma flet_side_scope : forall Γ k e0 e2,
  EXP Γ ⊢ plug_fs k (° ELet e0 e2) ->
  EXP (S Γ) ⊢ plug_fs (rename_framestack (fun n => S n) k) e2.
Proof.
  intros Γ k e0 e2 D.
  assert (D' : EXP Γ ⊢ ° ELet e0 e2) by (eapply plug_fs_extract_hole_scope; exact D).
  inv D'. inv H0.
  pose proof (rename_scope_add Γ 1 (plug_fs k (° ELet e0 e2)) D) as H1.
  rewrite <- plug_fs_rename in H1.
  cbn in H1.
  eapply plug_fs_hole_scope.
  exact H1.
  exact H3.
Qed.

Lemma plug_fs_CIU_case_compat : forall Γ k p e0 e2 e2' e3 e3',
  EXP Γ ⊢ plug_fs k (° ECase e0 p e2 e3) ->
  CIU_open (pat_vars p + Γ) (plug_fs (rename_framestack (fun n => pat_vars p + n) k) e2) e2' ->
  CIU_open Γ (plug_fs k e3) e3' ->
  CIU_open Γ (plug_fs k (° ECase e0 p e2 e3)) (° ECase e0 p e2' e3').
Proof.
  intros Γ k p e0 e2 e2' e3 e3' D Hexp2 Hexp3 ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (plug_fs k (° ECase e0 p e2 e3)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  assert (He2 : EXP (pat_vars p + Γ) ⊢ e2') by (eapply CIU_open_scope_r in Hexp2; eauto).
  assert (He3 : EXP Γ ⊢ e3') by (eapply CIU_open_scope_r in Hexp3; eauto).
  assert (Hclosed2 : EXPCLOSED (° ECase e0 p e2' e3').[ξ]). {
    apply -> subst_preserves_scope_exp. 2: eassumption.
    apply plug_fs_extract_hole_scope in D. repeat destruct_scope.
    do 2 constructor; eassumption.
  }
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  rewrite plug_fs_subst in HT.
  apply put_back_rev_fs in HT.
  destruct HT as [x HT2].
  inv HT2; subst.
  eapply term_eval_both in H5 as H5'. destruct H5' as [v0 [j [D1 D2]]].
  pose proof (terminates_step_any_2 j k0 _ _ H5 _ _ D2) as HT3.
  inv HT3.
  * apply ex_intro with (x := k1) in H7.
    apply put_back_fs in H7.

    assert (Hscope0 : SUBSCOPE pat_vars p + Γ ⊢ list_subst l ξ ∷ 0). {
      apply scoped_list_subscoped_eq. 2: assumption.
      2: by apply match_pattern_length in H1.
      eapply match_pattern_scoped in H1. exact H1.
      apply ex_intro with (x := j) in D1.
      apply step_any_closedness in D1. assumption. constructor.
      inv Hclosed2. inv H0. assumption.
    }
    pose proof (Hexp2 (list_subst l ξ) Hscope0) as [_ [_ Hcont]].
    specialize (Hcont F HF).
    pose proof rename_subst_core_framestack_list_subst k l ξ (pat_vars p)
      ltac:(by apply match_pattern_length in H1) as X.
    rewrite plug_fs_subst, X in Hcont. clear X.
    rewrite subst_comp, subst_list_extend in H7.
    2: by apply match_pattern_length in H1.
    specialize (Hcont H7) as [limit DD].

    eexists. simpl.
    constructor. eapply term_step_term_plus.
    eapply frame_indep_core in D1. exact D1.
    simpl. eapply term_case_true. eassumption.
    rewrite subst_comp, subst_list_extend. eassumption.
    by apply match_pattern_length in H1.
  * apply ex_intro with (x := k1) in H7.
    apply put_back_fs in H7.

    pose proof (Hexp3 ξ Hξ) as [_ [_ Hcont]].
    specialize (Hcont F HF).
    rewrite plug_fs_subst in Hcont.
    specialize (Hcont H7) as [limit DD].

    eexists. simpl.
    constructor. eapply term_step_term_plus.
    eapply frame_indep_core in D1. exact D1.
    simpl. eapply term_case_false. eassumption. eassumption.
Qed.

Lemma fcase_side_scope : forall Γ k e0 p e1 e2,
  EXP Γ ⊢ plug_fs k (° ECase e0 p e1 e2) ->
  EXP pat_vars p + Γ ⊢ plug_fs (rename_framestack (fun n => pat_vars p + n) k) e1.
Proof.
  intros Γ k e0 p e1 e2 D.
  assert (D' : EXP Γ ⊢ ° ECase e0 p e1 e2) by (eapply plug_fs_extract_hole_scope; exact D).
  inv D'. inv H0.
  pose proof (rename_scope_add Γ (pat_vars p) (plug_fs k (° ECase e0 p e1 e2)) D) as H1.
  rewrite <- plug_fs_rename in H1.
  cbn in H1.
  eapply plug_fs_hole_scope.
  exact H1.
  exact H5.
Qed.

(** [CIU_open] is transitive: lets us chain a "re-split without changing
    the plugged term" step (e.g. [introduce_let_CIU_cong] applied directly
    to the *original*, not-yet-reduced redex) with a small purely
    administrative reduction fact (e.g. [cons_val_CIU]/[let_cons_val_CIU]
    below), instead of needing a fully general "CIU is a context
    congruence" theorem. *)
Lemma CIU_open_trans : forall Γ e1 e2 e3,
  CIU_open Γ e1 e2 -> CIU_open Γ e2 e3 -> CIU_open Γ e1 e3.
Proof.
  intros Γ e1 e2 e3 H12 H23 ξ Hξ.
  pose proof (H12 ξ Hξ) as [Hc1 [Hc2 Hcont12]].
  pose proof (H23 ξ Hξ) as [_ [Hc3 Hcont23]].
  split.
  2: split.
  exact Hc1.
  exact Hc3.
  intros F HF HT.
  apply Hcont23; auto.
Qed.

(** Generalizes [cons_val_CIU] to an arbitrary surrounding continuation
    [k] (not just the empty/flat frame stack): [ECons] of two syntactic
    values is CIU-related to the [VCons] value it reduces to, *embedded in
    the same [k]*. Proved directly via [put_back_rev_fs]/[put_back_fs]
    (mirroring [flet_CIU_cong]'s technique) rather than by deriving a fully
    general "CIU_open is a context congruence" theorem: the 3-step [ECons]
    reduction happens identically regardless of what continuation surrounds
    it, so there is no need to reason about [FSCLOSED] of the intermediate
    popped stack. *)
Lemma cons_val_CIU_ctx : forall Γ k v1 v2,
  EXP Γ ⊢ plug_fs k (° ECons (˝ v1) (˝ v2)) ->
  VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 ->
  CIU_open Γ (plug_fs k (° ECons (˝ v1) (˝ v2))) (plug_fs k (˝ VCons v1 v2)).
Proof.
  intros Γ k v1 v2 D Hv1 Hv2 ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (plug_fs k (° ECons (˝ v1) (˝ v2))).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  assert (D2 : EXP Γ ⊢ plug_fs k (˝ VCons v1 v2))
    by (eapply plug_fs_hole_scope; [exact D | repeat constructor; auto]).
  assert (Hclosed2 : EXPCLOSED (plug_fs k (˝ VCons v1 v2)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  rewrite plug_fs_subst in HT |- *.
  cbn in HT |- *.
  apply put_back_rev_fs in HT.
  destruct HT as [x HT].
  apply put_back_fs.
  inv HT. inv H3. inv H4.
  exists k0.
  exact H3.
Qed.

(** [FCons2]'s own base case, when the continuation is empty: unlike
    [FApp1 []]/[FBIF1 []] (whose synthesized atom [EApp e []] is *the same*
    expression [introduce_let] hands back for [k = []]), [FCons2]'s atom is
    already a value [VCons v1 v2], so the [k = []] case isn't a syntactic
    no-op -- it needs this one-step (well, three machine steps) reduction
    fact instead of [CIU_open_refl]. *)
Lemma cons_val_CIU : forall Γ v1 v2,
  VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 ->
  CIU_open Γ (° ECons (˝ v1) (˝ v2)) (˝ VCons v1 v2).
Proof.
  intros Γ v1 v2 Hv1 Hv2 ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (° ECons (˝ v1) (˝ v2)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto; repeat constructor; auto).
  assert (Hclosed2 : EXPCLOSED (˝ VCons v1 v2).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto; repeat constructor; auto).
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  cbn in HT |- *.
  destruct HT as [y HT].
  inv HT. inv H3. inv H4.
  exists k.
  exact H3.
Qed.

(** Same idea as [cons_val_CIU], but with the extra [FLet] frame already
    wrapped around both sides -- this is the exact shape [FCons2]'s
    [introduce_let] "wildcard/[FLet]" 16-way dispatch needs, once composed
    (via [CIU_open_trans]) with [introduce_let_CIU_cong]/[flet_CIU_cong]
    applied directly to the original [ECons] redex (matching [D] exactly,
    no bridging needed there). *)
Lemma let_cons_val_CIU : forall Γ v1 v2 e,
  VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 -> EXP (S Γ) ⊢ e ->
  CIU_open Γ (° ELet (° ECons (˝ v1) (˝ v2)) e) (° ELet (˝ VCons v1 v2) e).
Proof.
  intros Γ v1 v2 e Hv1 Hv2 He ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (° ELet (° ECons (˝ v1) (˝ v2)) e).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto; repeat constructor; auto).
  assert (Hclosed2 : EXPCLOSED (° ELet (˝ VCons v1 v2) e).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto; repeat constructor; auto).
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  cbn in HT |- *.
  destruct HT as [y HT].
  inv HT.
  inv H3.
  inv H4.
  inv H3.
  exists (S k0).
  apply term_let.
  exact H4.
Qed.

(** ----------------------------------------------------------------- *)
(** * General "CIU is a context congruence" for value holes

  [normalize_exp]'s own [VFun] case recurses into the function *body*
  first, then re-runs [normalize_val] on the resulting [VFun vl body'] --
  a value that is CIU-*equivalent* to (not syntactically equal to) the
  original [VFun vl body]. None of the earlier compatibility lemmas
  ([introduce_let_CIU_cong], [plug_fs_CIU_let_compat],
  [plug_fs_CIU_case_compat], [cons_val_CIU_ctx]) apply here: they all
  relate a redex to *the thing it operationally reduces to* within [k],
  using [put_back]/[term_eval_both] to walk the machine forward. Here
  there is no reduction at all -- [VFun vl body] and [VFun vl e] are both
  already values, and the whole content differs only inside a closure
  that hasn't been (and may never be) called. This needs a genuine
  "plugging a CIU-related value into an arbitrary context preserves CIU"
  congruence, which for values reduces to: pop [k] down to a flat frame
  stack via [put_back_fs]/[put_back_rev_fs] (no evaluation phase needed,
  since a value is already "there"), then defer directly to the
  hypothesis at that frame stack. That needs [FSCLOSED] of the popped
  stack, which the earlier lemmas never had to establish (they always
  walked back down to the *original*, already-known-closed [F] before
  invoking any hypothesis). [plug_f_frame_closed]/[plug_fs_framestack_closed]
  below supply exactly that missing piece. *)

Lemma plug_f_frame_closed : forall f Γ e ξ,
  EXP Γ ⊢ plug_f f e -> SUBSCOPE Γ ⊢ ξ ∷ 0 -> FCLOSED (f.ₜ[ξ]).
Proof.
  destruct f; intros Γ e0 ξ D Hξ; cbn in *; inv D; inv H0.
  { constructor.
    apply Forall_map.
    apply indexed_to_forall with (def := ˝ VLit 0%Z).
    intros i Hi.
    apply -> subst_preserves_scope_exp; eauto. }
  { inv H2.
    constructor.
    - apply -> subst_preserves_scope_val; eauto.
    - apply Forall_map.
      apply indexed_to_forall with (def := VLit 0%Z).
      intros i Hi.
      apply -> subst_preserves_scope_val; eauto.
      assert (Hi' : i < base.length (map VVal l1 ++ e0 :: l2))
        by (rewrite length_app, length_map; lia).
      specialize (H3 i Hi').
      rewrite app_nth1 in H3 by (rewrite length_map; lia).
      rewrite map_nth in H3.
      inv H3. exact H1.
    - apply Forall_map.
      apply indexed_to_forall with (def := ˝ VLit 0%Z).
      intros i Hi.
      apply -> subst_preserves_scope_exp; eauto.
      assert (Hi' : S (base.length l1 + i) < base.length (map VVal l1 ++ e0 :: l2))
        by (rewrite length_app, length_map; cbn; lia).
      specialize (H3 (S (base.length l1 + i)) Hi').
      rewrite app_nth2 in H3 by (rewrite length_map; lia).
      rewrite length_map in H3.
      replace (S (base.length l1 + i) - base.length l1) with (S i) in H3 by lia.
      cbn in H3. exact H3. }
  { constructor.
    apply -> subst_preserves_scope_exp.
    exact H3.
    apply up_scope.
    exact Hξ. }
  { constructor.
    - apply -> subst_preserves_scope_exp.
      exact H5.
      assert (Hup : SUBSCOPE pat_vars p + Γ ⊢ upn (pat_vars p) ξ ∷ pat_vars p + 0)
        by (apply upn_scope; exact Hξ).
      rewrite Nat.add_0_r in Hup.
      exact Hup.
    - apply -> subst_preserves_scope_exp; eauto. }
  { constructor. apply -> subst_preserves_scope_exp; eauto. }
  { inv H3. constructor. apply -> subst_preserves_scope_val; eauto. }
  { constructor.
    apply Forall_map.
    apply indexed_to_forall with (def := ˝ VLit 0%Z).
    intros i Hi.
    apply -> subst_preserves_scope_exp; eauto. }
  { inv H2.
    constructor.
    - apply -> subst_preserves_scope_val; eauto.
    - apply Forall_map.
      apply indexed_to_forall with (def := VLit 0%Z).
      intros i Hi.
      apply -> subst_preserves_scope_val; eauto.
      assert (Hi' : i < base.length (map VVal l1 ++ e0 :: l2))
        by (rewrite length_app, length_map; lia).
      specialize (H3 i Hi').
      rewrite app_nth1 in H3 by (rewrite length_map; lia).
      rewrite map_nth in H3.
      inv H3. exact H1.
    - apply Forall_map.
      apply indexed_to_forall with (def := ˝ VLit 0%Z).
      intros i Hi.
      apply -> subst_preserves_scope_exp; eauto.
      assert (Hi' : S (base.length l1 + i) < base.length (map VVal l1 ++ e0 :: l2))
        by (rewrite length_app, length_map; cbn; lia).
      specialize (H3 (S (base.length l1 + i)) Hi').
      rewrite app_nth2 in H3 by (rewrite length_map; lia).
      rewrite length_map in H3.
      replace (S (base.length l1 + i) - base.length l1) with (S i) in H3 by lia.
      cbn in H3. exact H3. }
Qed.

Lemma plug_fs_framestack_closed : forall k Γ e ξ,
  EXP Γ ⊢ plug_fs k e -> SUBSCOPE Γ ⊢ ξ ∷ 0 -> FSCLOSED (k.ₖ[ξ]).
Proof.
  induction k as [|f k IH]; intros Γ e ξ D Hξ; cbn.
  - constructor.
  - constructor.
    + eapply plug_f_frame_closed. 2: exact Hξ.
      eapply plug_fs_extract_hole_scope. exact D.
    + eapply IH. 2: exact Hξ.
      exact D.
Qed.

(** [CIU_open] embedded via [plug_fs] into a context [k] is preserved when
    both sides are already *values* -- unlike [cons_val_CIU_ctx] (which
    needs 3 machine steps to turn a compound [ECons] redex into a value
    before it can "hand off" to [k]), a value hands off to [k] immediately
    ([put_back_rev_fs] alone gets us to the popped frame stack, with no
    [term_eval_both] detour needed), so the two sides' behaviors from that
    point on are governed entirely by the (given, closed) [CIU_open]
    hypothesis at the popped stack -- which is exactly what
    [plug_fs_framestack_closed] supplies. *)
Lemma val_CIU_ctx : forall Γ k v1 v2,
  EXP Γ ⊢ plug_fs k (˝ v1) ->
  CIU_open Γ (˝ v1) (˝ v2) ->
  CIU_open Γ (plug_fs k (˝ v1)) (plug_fs k (˝ v2)).
Proof.
  intros Γ k v1 v2 D Hciu ξ Hξ.
  assert (Hclosed1 : EXPCLOSED (plug_fs k (˝ v1)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  assert (Hv2 : EXP Γ ⊢ ˝ v2) by (eapply CIU_open_scope_r; eauto).
  assert (D2 : EXP Γ ⊢ plug_fs k (˝ v2))
    by (eapply plug_fs_hole_scope; [exact D | exact Hv2]).
  assert (Hclosed2 : EXPCLOSED (plug_fs k (˝ v2)).[ξ])
    by (apply -> subst_preserves_scope_exp; eauto).
  split. 2: split. 1-2: assumption.
  intros F HF HT.
  rewrite plug_fs_subst in HT |- *.
  apply put_back_rev_fs in HT.
  apply put_back_fs.
  pose proof (Hciu ξ Hξ) as [_ [_ Hcont]].
  apply Hcont.
  - apply Forall_app. split; auto.
    eapply plug_fs_framestack_closed; eauto.
  - exact HT.
Qed.

(** The "compatibility property of CIU ... from Erel" this whole section
    exists for: [normalize_exp]'s [VVal (VFun vl body)] case doesn't
    reduce anything to relate [body] and its normalized form [e] -- it
    just needs [VFun vl body] and [VFun vl e] to be CIU-related given
    [body ~ e] (CIU-related, one level up, self-reference plus [vl]
    arguments deeper). CIU_open itself has no compositional principle for
    this (it is defined purely contextually), so we go through
    [CIU_iff_Erel] to the step-indexed logical relation, where
    [Vrel_Fun_compat] (from [Compatibility.v], "we get from Erel") gives
    exactly this congruence, and convert back. *)
Lemma vfun_body_CIU_cong : forall Γ vl body e,
  CIU_open (S vl + Γ) body e ->
  CIU_open Γ (˝ VFun vl body) (˝ VFun vl e).
Proof.
  intros Γ vl body e Hbody.
  apply CIU_iff_Erel.
  apply Erel_Val_compat.
  eapply Vrel_Fun_compat.
  reflexivity.
  apply CIU_iff_Erel.
  exact Hbody.
Qed.

(** ----------------------------------------------------------------- *)
(** * Main theorem

  [FApp1] and [FBIF1]'s non-empty-list "shift" cases as well as [FApp2]'s
  and [FBIF2]'s "todo-shift" cases, and [FCase]/[FCons1] (all
  administrative: they re-split (e,k) without changing the plugged term)
  are closed the same way as the outer levels via [IHfuel] directly.
  [FApp1]/[FApp2]'s "introduce a let" cases are closed via
  [introduce_let_CIU_cong]/[introduce_let_side_scope] above (verified in
  full; the identical two lines close [FCase]/[FCons1]/[FCons2]/[FBIF1]/
  [FBIF2] too, since those lemmas are generic in the frame).

  The [VVal (VFun vl body)] case needs its own explanation: it normalizes
  the closure's *body* first (via [IHfuel], recursing into [normalize_exp]
  on [body] with an empty stack) and only then re-runs [normalize_val] on
  the resulting [VFun vl body']. Unlike every other case here, [IHfuel]
  can't finish the job on its own: [normalize_val fuel (VFun vl body') k]
  is a hypothesis about [normalize_val], not [normalize_exp], so it isn't
  literally an instance of [IHfuel] (which is stated purely in terms of
  [normalize_exp]) -- and [body'] is only CIU-*equivalent* to [body], not
  syntactically equal, so none of the "redex reduces to X" compatibility
  lemmas above apply either (there is no reduction at all: [VFun vl body]
  and [VFun vl body'] are both already values). What's needed is: (1) a
  standalone statement of "[normalize_val] preserves CIU", proved by
  literally the same argument as the sibling ["-" (normalize_val)] case
  below (this is [ValPart], asserted once, at this same [fuel] level, and
  shared by both branches of the [extract_VFun] split -- since it depends
  on [IHfuel] but not on which branch we're in, it doesn't need its own
  separate top-level lemma/induction); and (2) a genuine "CIU is a context
  congruence" fact for the [VFun vl body ~ VFun vl body'] step itself,
  which is [val_CIU_ctx] composed with [vfun_body_CIU_cong] (the latter
  gets the [VFun body ~ VFun body'] compatibility from [Vrel_Fun_compat]
  via [CIU_iff_Erel] -- "the compatibility properties of CIU ... from
  Erel").
*)
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
  * (* Main assertion - reused for fun and normal vals too *)
    assert (ValPart : forall Γ k v anf,
      EXP Γ ⊢ plug_fs k (˝ v) ->
      normalize_val fuel v k = Some anf ->
      CIU_open Γ (plug_fs k (˝ v)) anf).
    { clear -IHfuel.
      intros Γ k v anf D H.
      destruct fuel; simpl in *; try congruence.
      destruct k. 2: destruct f. all: simpl in *.
      + inv H. simpl. apply CIU_open_refl. assumption.
      (* FApp1 *)
      + destruct l.
        ** unfold introduce_let in H; destruct k; simpl in *; inv H.
           1: by apply CIU_open_refl.
           destruct extract_Flet eqn:Y; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           all: eapply IHfuel in Hexp; try lia; cbn in *.
           -- destruct f; inv Y. cbn.
              eapply (plug_fs_CIU_let_compat Γ k (° EApp (˝ v) []) e).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- destruct f; inv Y. cbn.
              eapply (flet_side_scope Γ k (° EApp (˝ v) []) e). simpl in *.
              exact D.
           -- eapply (introduce_let_CIU_cong Γ (f::k) (° EApp (˝ v) [])).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- cbn.
              eapply (introduce_let_side_scope Γ (f::k) (° EApp (˝ v) [])).
              exact D.
        ** eapply IHfuel in H; [ simpl in H; eassumption | lia | by simpl ].
      (* FApp2 *)
      + destruct l2.
        ** unfold introduce_let in H; destruct k; simpl in *; inv H.
           1: by apply CIU_open_refl.
           destruct extract_Flet eqn:Y; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           all: eapply IHfuel in Hexp; try lia; cbn in *.
           -- destruct f; inv Y. cbn.
              eapply (plug_fs_CIU_let_compat Γ k (° EApp (˝ v0) (map VVal l1 ++ [˝v])) e).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- destruct f; inv Y. cbn.
              eapply (flet_side_scope Γ k (° EApp (˝ v0) (map VVal l1 ++ [˝v])) e). simpl in *.
              exact D.
           -- eapply (introduce_let_CIU_cong Γ (f::k) (° EApp (˝ v0) (map VVal l1 ++ [˝v]))).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- cbn.
              eapply (introduce_let_side_scope Γ (f::k) (° EApp (˝ v0) (map VVal l1 ++ [˝v]))).
              exact D.
        ** eapply IHfuel in H; [ simpl in H | lia | simpl ].
           -- by rewrite map_app, <- app_assoc in H.
           -- by rewrite map_app, <- app_assoc.
      (* FLet *)
      + destruct normalize_exp eqn:Hexp in H; inv H.
        eapply (plug_fs_CIU_let_compat Γ k (˝ v) e2).
        ** exact D.
        ** eapply (IHfuel fuel).
           lia.
           eapply (flet_side_scope Γ k (˝ v) e2).
           exact D.
           exact Hexp.
      (* FCase *)
      + destruct normalize_exp eqn:Hexp1 in H; inv H.
        ** destruct normalize_exp eqn:Hexp2 in H1; inv H1.
           apply plug_fs_extract_hole_scope in D as Dscope. repeat destruct_scope.
           eapply IHfuel with (Γ := Γ) in Hexp1. 2: lia.
           2: {
             eapply plug_fs_hole_scope. exact D. assumption.
           }
           eapply IHfuel with (Γ := pat_vars p + Γ) in Hexp2. 2: lia.
           2: {
             eapply fcase_side_scope. eassumption.
           }
           eapply plug_fs_CIU_case_compat; eassumption.
        ** destruct normalize_exp in H1; simpl in H1; congruence.
      (* FCons1 *)
      + eapply IHfuel in H; try lia; by simpl in *.
      (* FCons2 *)
      + unfold introduce_let in H; destruct k; simpl in *; inv H.
        ** intros ξ Hξ. simpl. apply CIU_eval.
           repeat destruct_scope.
           do 3 constructor; apply -> subst_preserves_scope_val; eassumption.
           eexists. repeat econstructor.
        ** destruct extract_Flet eqn:Y; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           -- destruct f; inv Y; cbn.
              apply plug_fs_extract_hole_scope in D as Dscope.
              apply plug_f_extract_hole_scope in Dscope. repeat destruct_scope.
              eapply IHfuel with (Γ := S Γ) in Hexp; try lia; cbn in *.
              2: {
                eapply flet_side_scope. eassumption.
              }
              apply CIU_open_scope_r in Hexp as He0.
              pose proof let_cons_val_CIU Γ v v2 e0 H1 H0 He0 as T2.
              epose proof plug_fs_CIU_let_compat Γ k _ _ _ _ Hexp as T1.
              eapply CIU_open_trans. exact T1. exact T2.
              Unshelve. assumption.
           -- eapply IHfuel in Hexp; try lia; cbn in *.
              apply plug_fs_extract_hole_scope in D as Dscope.
              apply plug_f_extract_hole_scope in Dscope. repeat destruct_scope.
              eapply CIU_open_trans.
              apply (cons_val_CIU_ctx _ (f::k)); try eassumption.
              cbn. eassumption.
              eapply (plug_fs_hole_scope (f::k)). exact D.
              apply plug_fs_extract_hole_scope, plug_f_extract_hole_scope in D.
              repeat destruct_scope. by do 2 constructor.
      (* FBIF1 *)
      + destruct l.
        ** unfold introduce_let in H; destruct k; simpl in *; inv H.
           1: by apply CIU_open_refl.
           destruct extract_Flet eqn:Y; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           all: eapply IHfuel in Hexp; try lia; cbn in *.
           -- destruct f; inv Y. cbn.
              eapply (plug_fs_CIU_let_compat Γ k (° EBIF (˝ v) []) e).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- destruct f; inv Y. cbn.
              eapply (flet_side_scope Γ k (° EBIF (˝ v) []) e). simpl in *.
              exact D.
           -- eapply (introduce_let_CIU_cong Γ (f::k) (° EBIF (˝ v) [])).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- cbn.
              eapply (introduce_let_side_scope Γ (f::k) (° EBIF (˝ v) [])).
              exact D.
        ** eapply IHfuel in H; [ simpl in H; eassumption | lia | by simpl ].
      (* FBIF2 *)
      + destruct l2.
        ** unfold introduce_let in H; destruct k; simpl in *; inv H.
           1: by apply CIU_open_refl.
           destruct extract_Flet eqn:Y; simpl in H1; destruct normalize_exp eqn:Hexp in H1;
             inv H1; simpl in *; try congruence.
           all: eapply IHfuel in Hexp; try lia; cbn in *.
           -- destruct f; inv Y. cbn.
              eapply (plug_fs_CIU_let_compat Γ k (° EBIF (˝ v0) (map VVal l1 ++ [˝v])) e).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- destruct f; inv Y. cbn.
              eapply (flet_side_scope Γ k (° EBIF (˝ v0) (map VVal l1 ++ [˝v])) e). simpl in *.
              exact D.
           -- eapply (introduce_let_CIU_cong Γ (f::k) (° EBIF (˝ v0) (map VVal l1 ++ [˝v]))).
              exact D.
              apply plug_fs_extract_hole_scope in D.
              by apply plug_f_extract_hole_scope in D.
           -- cbn.
              eapply (introduce_let_side_scope Γ (f::k) (° EBIF (˝ v0) (map VVal l1 ++ [˝v]))).
              exact D.
        ** eapply IHfuel in H; [ simpl in H | lia | simpl ].
           -- by rewrite map_app, <- app_assoc in H.
           -- by rewrite map_app, <- app_assoc.
    }
    (* Now, we finish with the two value-based branches *)
    destruct extract_VFun eqn:X.
    - destruct p as [vl body].
      destruct v; inv X.
      destruct normalize_exp eqn:Hexp0 in H; inv H.
      eapply IHfuel in Hexp0. 2: lia.
      2: {
        simpl. apply plug_fs_extract_hole_scope in D. inv D. inv H0.
        exact H2.
      } cbn in Hexp0.
      eapply CIU_open_trans.
      apply val_CIU_ctx. exact D. apply vfun_body_CIU_cong. exact Hexp0.
      apply ValPart.
      + eapply plug_fs_hole_scope. exact D. constructor. constructor.
        eapply CIU_open_scope_r. exact Hexp0.
      + exact H1.
    - apply (ValPart Γ k v anf D H).
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
Lemma normalize_preserves_semantics_wrong fuel : forall k e anf v,
  ⟨k, e⟩ -->* v ->
  normalize_exp fuel e k = Some anf ->
  ⟨[], anf⟩ -->* v.
Proof.
Abort.
