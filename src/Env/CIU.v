From CoreErlang Require Export Env.Termination
                               Env.Scoping.



Definition CIU_open (n : nat) (e1 e2 : Exp) :=
  EXP n ⊢ e1 /\ EXP n ⊢ e2 /\
  forall Γ, length Γ = n /\
  forall Fs, FSCLOSED Fs ->
    | Γ, Fs, e1 | ↓ -> | Γ, Fs, e2 | ↓.


Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  unfold CIU_open in H; by intuition.
Qed.

Lemma CIU_open_scope_l : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_r : core.

Theorem CIU_eval : forall e1 v Γ,
  EXP length Γ ⊢ e1 ->
  ⟨ Γ, [], e1 ⟩ -->* v ->
    CIU_open (length Γ) e1 v /\ CIU_open (length Γ) v e1.
Proof.
  intros. repeat split; try auto.
  
Qed.

