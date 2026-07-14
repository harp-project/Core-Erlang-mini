From CoreErlang.Subst Require Export Semantics.
From CoreErlang.Subst Require Import SemanticProperties.
From Coq Require Import Lia.

Import ListNotations.

Open Scope sub_scope.

Definition deterministic_step (fs : FrameStack) (e : Exp)
  : option (FrameStack * Exp) :=
  match e with
  | VVal v =>
      match fs with
      | [] => None
      | FApp1 (hd :: tl) :: xs =>
          Some ((FApp2 v [] tl) :: xs, hd)
      | FApp1 [] :: xs =>
          match v with
          | VFun 0 e' => Some (xs, e'.[VFun 0 e'/])
          | _ => None
          end
      | FApp2 v0 vs tl :: xs =>
          match tl with
          | hd :: tl => Some ((FApp2 v0 (vs ++ [v]) tl) :: xs, hd)
          | [] => match v0 with
                  | (VFun vl e') =>
                    if Nat.eqb vl (S (length vs))
                    then Some (xs, e'.[list_subst (VFun vl e' :: (vs ++ [v])) idsubst])
                    else None
                  | _ => None
                  end
          end
      | FBIF1 (hd :: tl) :: xs =>
          Some ((FBIF2 v [] tl) :: xs, hd)
      | FBIF1 [] :: _ => None
      | FBIF2 v0 vs tl :: xs =>
        match tl with
        | hd::tl => Some ((FBIF2 v0 (vs ++ [v]) tl) :: xs, hd)
        | [] => match v0, vs, v with
                | (VLit "+"%string), [VLit (Int i1)], VLit (Int i2) =>
                  Some (xs, VVal (VLit (Z.add i1 i2)))
                | _, _, _ => None
                end
        end
      | FLet e2 :: xs =>
          Some (xs, e2.[v/])
      | FCase p e2 e3 :: xs =>
          match match_pattern p v with
          | Some l => Some (xs, e2.[list_subst l idsubst])
          | None => Some (xs, e3)
          end
      | FCons1 e1 :: xs =>
          Some (FCons2 v :: xs, e1)
      | FCons2 v2 :: xs =>
          Some (xs, VVal (VCons v v2))
      end
  | EExp nv =>
      match nv with
      | ELet e1 e2 =>
          Some (FLet e2 :: fs, e1)
      | EApp e0 el =>
          Some (FApp1 el :: fs, e0)
      | EBIF name params =>
          Some (FBIF1 params :: fs, name)
      | ECase e0 p e1 e2 =>
          Some (FCase p e1 e2 :: fs, e0)
      | ECons e1 e2 =>
          Some (FCons1 e1 :: fs, e2)
      | EReceive _ =>
          None
      end
  end.

Fixpoint deterministic_step_limit (k : nat) (fs : FrameStack) (e : Exp)
  : FrameStack * Exp :=
  match k with
  | 0 => (fs, e)
  | S k' =>
      match deterministic_step fs e with
      | Some (fs', e') => deterministic_step_limit k' fs' e'
      | None => (fs, e)
      end
  end.

Ltac invSome :=
  match goal with
  | H : Some _ = Some _ |- _ => inv H
  | H : (_, _) = (_, _) |- _ => inv H
  | H : Some _ = None |- _ => inv H
  | H : None = Some _ |- _ => inv H
  end.

Theorem deterministic_step_complete :
  forall fs e fs' e',
    ⟨ fs, e ⟩ --> ⟨ fs', e' ⟩ ->
    deterministic_step fs e = Some (fs', e').
Proof.
  intros. inversion H; subst; simpl; try reflexivity.
  by rewrite Nat.eqb_refl.
  all: by rewrite H0.
Qed.

Theorem deterministic_step_sound :
  forall fs e fs' e',
    deterministic_step fs e = Some (fs', e') ->
    ⟨ fs, e ⟩ --> ⟨ fs', e' ⟩.
Proof.
  intros. unfold deterministic_step in H; repeat case_match; subst; simpl in *.
  all: invSome; try by constructor.
  econstructor. by apply Nat.eqb_eq in H5.
Qed.

