Require Import LogRel.
Import ListNotations.

(* Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (p : is_value v) (l1 l2 : list Exp) (p2 : forall e, In e l2 -> is_value e) (** Can be problematic *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (p : is_value v) (* v + □ *)
| FIf (e2 e3 : Exp) (* if □ then e2 else e3 *).

Definition merge (F : Frame) (e : Exp) :=
match F with
 | FApp1 l => 
 | FApp2 v p l1 l2 p2 => _
 | FLet v e2 => _
 | FPlus1 e2 => _
 | FPlus2 v p => _
 | FIf e2 e3 => _
end


Definition FrameStack := list Frame.

Inductive Configuration : Type :=
| ConfigReady (e : Exp)
| ConfigStep (e : Exp) (F : FrameStack).

Definition step (c : Configuration) : option Configuration :=
match c with
| ConfigReady e => None (* Should not be this ID? *)
| ConfigStep e F =>
  match e with
  | ELit l =>
    match F with
    | [] => ConfigReady (ELit l)
    | f::fs => ConfigStep (merge f (ELit l)) fs
    end
  | EVar v => _
  | EFunId f => _
  | EFun vl e => _
  | ERecFun f vl e => _
  | EApp exp l => _
  | ELet v e1 e2 => _
  | ELetRec f vl b e => _
  | EPlus e1 e2 => _
  | EIf e1 e2 e3 => _
  end
end. *)


Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall v1 clock,
  eval clock e1 = Res v1 -> (exists v2, exists clock, eval clock e2 = Res v2 /\ equivalent_values v1 v2).

Definition CIU_open (Γ : list VarFunId) (e1 e2 : Exp) :=
  forall ξ, subscoped Γ [] ξ ->
  CIU (subst ξ e1) (subst ξ e2).

Lemma CIU_closed :
  forall e1 e2,
  CIU e1 e2 -> EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.

Lemma CIU_closed_l : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Hint Resolve CIU_closed_l.

Lemma CIU_closed_r : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Hint Resolve CIU_closed_r.

Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  unfold CIU_open in H.
  split;
    eapply sub_implies_scope_exp; eauto.
Qed.

Lemma CIU_open_scope_l : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Hint Resolve CIU_open_scope_l.

Lemma CIU_open_scope_r : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Hint Resolve CIU_open_scope_r.

Lemma Erel_implies_CIU : forall Γ e1 e2,
  Erel_open Γ e1 e2 ->
  CIU_open Γ e1 e2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split; [|split].
  - eapply subst_preserves_scope_rev; eauto.
  - eapply subst_preserves_scope_rev; eauto.
  - intros. unfold Erel_open, Erel, exp_rel in H.
    (* Vrel reflexivity needed *)
Qed.
