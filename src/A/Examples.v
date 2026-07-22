From CoreErlang.Subst Require Import Syntax.
From CoreErlang.A Require Import SubstDeterministic.
From CoreErlang.A Require Import Syntax.

Import ListNotations.

Open Scope sub_scope.
Open Scope string_scope.

(** Standard ANF examples, following the usual discipline from the
    literature: operators, operands, and case scrutinees are atomic,
    and intermediate computations are named left-to-right with [let]. *)

Definition anf_bif_args_src : Exp :=
  EBIF (VLit "+"%string)
    [°EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z];
     °EBIF (VLit "+"%string) [˝VLit 3%Z; ˝VLit 4%Z]].

Definition anf_bif_args_anf : Exp :=
  ELet (EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z])
    (ELet (EBIF (VLit "+"%string) [˝VLit 3%Z; ˝VLit 4%Z])
      (EBIF (VLit "+"%string) [˝VVar 1; ˝VVar 0])).

Definition anf_case_scrutinee_src : Exp :=
  ECase (°EBIF (VLit "+"%string) [˝VLit 2%Z; ˝VLit (-2)%Z])
    (PLit 0%Z)
    (VLit 1%Z)
    (VLit 0%Z).

Definition anf_case_scrutinee_anf : Exp :=
  ELet (EBIF (VLit "+"%string) [˝VLit 2%Z; ˝VLit (-2)%Z])
    (ECase (VVar 0) (PLit 0%Z) (VLit 1%Z) (VLit 0%Z)).

Definition anf_app_arg_src : Exp :=
  EApp
    (VFun 1 (EBIF (VLit "+"%string) [˝VVar 1; ˝VLit 1%Z]))
    [°EBIF (VLit "+"%string) [˝VLit 40%Z; ˝VLit 2%Z]].

Definition anf_app_arg_anf : Exp :=
  ELet (EBIF (VLit "+"%string) [˝VLit 40%Z; ˝VLit 2%Z])
    (EApp (VFun 1 (EBIF (VLit "+"%string) [˝VVar 1; ˝VLit 1%Z]))
      [˝VVar 0]).

Definition anf_nested_let_src : Exp :=
  ELet (EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z])
    (EBIF (VLit "+"%string)
      [˝VVar 0;
       °EBIF (VLit "+"%string) [˝VLit 3%Z; ˝VLit 4%Z]]).

Definition anf_nested_let_anf : Exp :=
  ELet (EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z])
    (ELet (EBIF (VLit "+"%string) [˝VLit 3%Z; ˝VLit 4%Z])
      (EBIF (VLit "+"%string) [˝VVar 1; ˝VVar 0])).

Definition anf_case_branch_src : Exp :=
  ECase (VLit 0%Z) (PLit 0%Z)
    (EBIF (VLit "+"%string)
      [°EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z];
       ˝VLit 5%Z])
    (VLit 9%Z).

Definition anf_case_branch_anf : Exp :=
  ECase (VLit 0%Z) (PLit 0%Z)
    (ELet (EBIF (VLit "+"%string) [˝VLit 1%Z; ˝VLit 2%Z])
      (EBIF (VLit "+"%string) [˝VVar 0; ˝VLit 5%Z]))
    (VLit 9%Z).

Definition anf_examples : list (Exp * Exp) :=
  [ (anf_bif_args_src, anf_bif_args_anf)
  ; (anf_case_scrutinee_src, anf_case_scrutinee_anf)
  ; (anf_app_arg_src, anf_app_arg_anf)
  ; (anf_nested_let_src, anf_nested_let_anf)
  ; (anf_case_branch_src, anf_case_branch_anf)
  ].

(* Compute A_normalize_heat_compatible anf_bif_args_src.
Compute A_normalize_reduce ([AHeatEval (FBIF2 (VLit "+") []
              [° (EBIF (VLit "+") [˝VLit 3%Z; ˝VLit 4%Z])])])
              (EBIF (VLit "+") [˝VLit 1%Z; ˝VLit 2%Z]).
Compute A_normalize_heat_compatible (° ELet
(° EBIF (˝ VLit "+") [˝ VLit 1%Z;
˝ VLit 2%Z])
(° EBIF (˝ VLit "+")
[˝ VVar 0;
° EBIF (˝ VLit "+")
[˝ VLit 3%Z; ˝ VLit 4%Z]])).
Compute A_normalize_reduce [AHeatLetBody
(° EBIF (˝ VLit "+") [˝ VLit 1%Z; ˝ VLit
2%Z]);
AHeatEval (FBIF2 (VLit "+") [VVar 0] [])] (° EBIF (˝ VLit "+") [˝ VLit 3%Z; ˝ VLit 4%Z]).
Compute A_normalize_heat_compatible (° ELet
(° EBIF (˝ VLit "+") [˝ VLit 3%Z;
˝ VLit 4%Z])
(° ELet
(° EBIF (˝ VLit "+")
[˝ VLit 1%Z; ˝ VLit 2%Z])
(° EBIF (˝ VLit "+")
[˝ VVar 0; ˝ VVar 0]))). *)

Notation "'let' e1 'in' e2" := (ELet e1 e2) (only printing, at level 70, e2 at level 10).
Notation "'call' e1 ( e2 ; e3 ; .. ; en )" := (EBIF e1 (cons e2 (cons e3 .. (cons en nil) .. )) ) (only printing, at level 70).


(** Goals verifying each ANF example normalizes correctly *)
Lemma anf_bif_args_goal :
  normalize_exp 1000 anf_bif_args_src NCHole = Some anf_bif_args_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_case_scrutinee_goal :
  normalize_exp 1000 anf_case_scrutinee_src NCHole = Some anf_case_scrutinee_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_app_arg_goal :
   normalize_exp 1000 anf_app_arg_src NCHole = Some anf_app_arg_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_nested_let_goal :
  normalize_exp 1000 anf_nested_let_src NCHole = Some anf_nested_let_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_case_branch_goal :
  normalize_exp 1000 anf_case_branch_src NCHole = Some anf_case_branch_anf.
Proof.
  cbv. reflexivity.
Qed.
