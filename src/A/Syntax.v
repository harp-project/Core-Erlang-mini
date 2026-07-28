From CoreErlang.Subst Require Export Semantics CIU.
From stdpp Require Export base list.

Inductive ANF : Exp -> Prop :=
| anf_val (v : Val) :
  ANF (˝v)

| anf_let (v : Val) (e2 : Exp) :
  ANF e2 ->
  ANF (°ELet v e2)

| anf_case p (v : Val) (e1 e2 : Exp) :
  ANF e1 -> ANF e2 ->
  ANF (°ECase v p e1 e2)

| anf_app (v : Val) (vl : list Val) :
  ANF (°EApp v (map VVal vl))

| anf_bif (v : Val) (vl : list Val) :
  ANF (°EBIF v (map VVal vl))

| anf_let_app (v : Val) (vl : list Val) (e2 : Exp) :
  ANF e2 ->
  ANF (°ELet (°EApp v (map VVal vl)) e2)

| anf_let_bif (v : Val) (vl : list Val) (e2 : Exp) :
  ANF e2 ->
  ANF (°ELet (°EBIF v (map VVal vl)) e2)
.

Definition rename_frame (ρ : Renaming) (f : Frame) : Frame :=
match f with
 | FApp1 l => FApp1 (map (rename ρ) l)
 | FApp2 v l1 l2 => FApp2 (rename_val ρ v) (map (rename_val ρ) l1) (map (rename ρ) l2)
 | FLet e2 => FLet (rename (upren ρ) e2)
 | FCase p e2 e3 => FCase p (rename (uprenn (pat_vars p) ρ) e2) (rename ρ e3)
 | FCons1 e1 => FCons1 (rename ρ e1)
 | FCons2 v2 => FCons2 (rename_val ρ v2)
 | FBIF1 l => FBIF1 (map (rename ρ) l)
 | FBIF2 v l1 l2 => FBIF2 (rename_val ρ v) (map (rename_val ρ) l1) (map (rename ρ) l2)
end.


Definition rename_framestack (ρ : Renaming) (Fs : FrameStack) : FrameStack :=
  map (rename_frame ρ) Fs.

Fixpoint take_while {A : Type} (f : A -> bool) (l : list A) : list A :=
match l with
| [] => []
| x::xs => if f x then x::take_while f xs else []
end.

Fixpoint drop_while {A : Type} (f : A -> bool) (l : list A) : list A :=
match l with
| [] => []
| x::xs => if f x then drop_while f xs else xs
end.

Definition is_value (e : Exp) : bool :=
match e with
 | EExp e => false
 | VVal v => true
end.

Definition normalize_name (f : (Exp -> Exp) -> Exp) (k : Exp -> Exp) : Exp :=
  f (fun e' => if is_value e' then k e' else ELet e' (k (VVar 0))).

Fixpoint normalize (e : Exp) (k : Exp -> Exp) {struct e} : Exp :=
match e with
| VVal (VFun vl e) => k (VVal (VFun vl (normalize e id)))
| VVal (VCons e1 e2) => k e (* TODO: might be wrong/should not occur *)
| VVal v => k (VVal v)
| EExp (ELet e1 e2) => normalize e1 (fun e1' => ELet e1' (normalize e2 k))
| EExp (ECase e p e1 e2) => normalize_name (normalize e) (fun t => k (ECase t p (normalize e1 k) (normalize e2 k)))
| EExp (EApp e1 l) => normalize_name (normalize e1) (fun e1' =>
     (fix normalize_name_star (l : list Exp) (k : list Exp -> Exp) {struct l} : Exp :=
      match l with
      | [] => k []
      | e::es => normalize_name (normalize e) (fun e' => normalize_name_star es (fun es' => k (e'::es')))
      end) l (fun l' => k (EApp e1' l')))
| EExp (EBIF e1 l) => normalize_name (normalize e1) (fun e1' => 
     (fix normalize_name_star (l : list Exp) (k : list Exp -> Exp) {struct l} : Exp :=
      match l with
      | [] => k []
      | e::es => normalize_name (normalize e) (fun e' => normalize_name_star es (fun es' => k (e'::es')))
      end) l (fun l' => k (EBIF e1' l')))
| EExp (ECons e1 e2) => normalize_name (normalize e2) (fun e2' => normalize_name (normalize e1) (fun e1' => k (ECons e1' e2')))
| EExp (EReceive l) => inf (* TODO option? *)
end.

Definition normalize_term (e : Exp) : Exp := normalize e id.

Definition introduce_let  (normalize_exp : Exp -> FrameStack -> option Exp) 
                          (k : FrameStack) (e : Exp) : option Exp :=
match k with
| [] => Some e
| FLet e2 :: k' =>
    fmap (fun e2' => EExp (ELet e e2')) (normalize_exp e2 k')
| _ => if is_value e
       then normalize_exp e k
       else fmap (fun e' => EExp (ELet e e'))
            (normalize_exp (VVar 0) (rename_framestack (fun n => S n) k))
end.

Fixpoint normalize_exp (fuel : nat) (e : Exp) (k : FrameStack) : option Exp :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match e with
      | VVal (VFun vl body) =>
          mbind (fun body' =>
          normalize_val fuel' (VFun vl body') k)
          (normalize_exp fuel' body [])
      | VVal v => normalize_val fuel' v k
      | EExp (ELet e1 e2) => normalize_exp fuel' e1 (FLet e2 :: k)
      | EExp (ECase e0 p e1 e2) =>
          normalize_exp fuel' e0 (FCase p e1 e2 :: k)
      | EExp (EApp f args) => normalize_exp fuel' f (FApp1 args :: k)
      | EExp (EBIF f args) => normalize_exp fuel' f (FBIF1 args :: k)
      | EExp (ECons e1 e2) => normalize_exp fuel' e2 (FCons1 e1 :: k)
      | EExp (EReceive cases) => None
      (*  continue_ctx_fuel fuel' k (EReceive cases) *)
      end
  end
with normalize_val (fuel : nat) (e : Val) (k : FrameStack) : option Exp :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match k with
      | [] => Some (VVal e)
      | FLet e2 :: k' =>
          fmap (fun e2' => EExp (ELet e e2')) (normalize_exp fuel' e2 k')
      | FCase p e1 e2 :: k' =>
          mbind (fun e1' =>
            fmap (fun e2' => EExp (ECase e p e1' e2'))
            (normalize_exp fuel' e2 k'))
          (normalize_exp fuel' e1 k')
      | FApp1 [] :: k' =>
          introduce_let (normalize_exp fuel') k' (EApp e [])
      | FApp1 (f::args) :: k' => 
          normalize_exp fuel' f (FApp2 e [] args :: k')
      | FApp2 f done (fe::todo') :: k' =>
          normalize_exp fuel' fe (FApp2 f (done ++ [e]) todo' :: k')
      | FApp2 f done [] :: k' =>
          introduce_let (normalize_exp fuel') k' (EApp f (map VVal done ++ [VVal e]))
      | FBIF1 [] :: k' =>
          introduce_let (normalize_exp fuel') k' (EBIF e [])
      | FBIF1 (f::args) :: k' => 
          normalize_exp fuel' f (FBIF2 e [] args :: k')
      | FBIF2 f done (fe::todo') :: k' =>
          normalize_exp fuel' fe (FBIF2 f (done ++ [e]) todo' :: k')
      | FBIF2 f done [] :: k' =>
          introduce_let (normalize_exp fuel') k' (EBIF f (map VVal done ++ [VVal e]))
      | FCons1 e1 :: k' =>
          normalize_exp fuel' e1 (FCons2 e :: k')
      | FCons2 e2 :: k' =>
          introduce_let (normalize_exp fuel') k' (VCons e e2)
      end
  end.

Section Examples.

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

Notation "'let' e1 'in' e2" := (ELet e1 e2) (only printing, at level 70, e2 at level 10).
Notation "'call' e1 ( e2 ; e3 ; .. ; en )" := (EBIF e1 (cons e2 (cons e3 .. (cons en nil) .. )) ) (only printing, at level 70).


(** Goals verifying each ANF example normalizes correctly *)
Lemma anf_bif_args_goal :
  normalize_exp 1000 anf_bif_args_src [] = Some anf_bif_args_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_case_scrutinee_goal :
  normalize_exp 1000 anf_case_scrutinee_src [] = Some anf_case_scrutinee_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_app_arg_goal :
   normalize_exp 1000 anf_app_arg_src [] = Some anf_app_arg_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_nested_let_goal :
  normalize_exp 1000 anf_nested_let_src [] = Some anf_nested_let_anf.
Proof.
  cbv. reflexivity.
Qed.

Lemma anf_case_branch_goal :
  normalize_exp 1000 anf_case_branch_src [] = Some anf_case_branch_anf.
Proof.
  cbv. reflexivity.
Qed.

End Examples.


Fixpoint size_exp (e : Exp) : nat :=
  match e with
  | EExp ne =>
      S (match ne with
         | EApp e1 args =>
             size_exp e1 + foldr (fun x acc => size_exp x + acc) 0 args
         | ELet e1 e2 => size_exp e1 + size_exp e2
         | ECase e1 _ e2 e3 => size_exp e1 + size_exp e2 + size_exp e3
         | ECons e1 e2 => size_exp e1 + size_exp e2
         | EReceive cases =>
             foldr (fun '(_, e) acc => size_exp e + acc) 0 cases
         | EBIF e1 args =>
             size_exp e1 + foldr (fun x acc => size_exp x + acc) 0 args
         end)
  | VVal v => S (size_val v)
  end
with size_val (v : Val) : nat := (* technical *)
  match v with
  | VLit _ => 1
  | VPid _ => 1
  | VVar _ => 1
  | VFun _ e => S (size_exp e)
  | VNil => 1
  | VCons v1 v2 => S (size_val v1 + size_val v2)
  end.

Lemma Private_size_rename :
  (forall e ρ, size_exp (rename ρ e) = size_exp e) /\
  (forall e ρ, size_exp (rename_nonval ρ e) = size_exp e) /\
  (forall e ρ, size_val (rename_val ρ e) = size_val e).
Proof.
  apply Exp_full_ind with
    (Q := Forall (fun e => forall ρ, size_exp (rename ρ e) = size_exp e))
    (W := Forall (fun '(_, e) => forall ρ, size_exp (rename ρ e) = size_exp e))
  ; simpl; intros; try lia.
  * by rewrite H.
  * rewrite H. lia.
  * rewrite H. lia.
  * rewrite H. f_equal. f_equal.
    induction H0; simpl. lia.
    rewrite H0. f_equal. assumption.
  * rewrite H, H0. lia.
  * rewrite H, H0, H1. lia.
  * rewrite H, H0. lia.
  * rewrite H, H0. lia.
  * rewrite H. f_equal. f_equal.
    induction H0; simpl. lia.
    rewrite H0. f_equal. assumption.
  * f_equal.
    induction H; simpl. lia. destruct x.
    rewrite H. f_equal. assumption.
  * constructor.
  * by constructor.
  * constructor.
  * by constructor.
Qed.

Lemma size_rename :
  (forall e ρ, size_exp (rename ρ e) = size_exp e).
Proof.
  apply Private_size_rename.
Qed.

Lemma size_rename_val :
  (forall e ρ, size_val (rename_val ρ e) = size_val e).
Proof.
  apply Private_size_rename.
Qed.

Lemma fold_size_exp_rename :
  forall ρ l,
    foldr (fun x acc => size_exp x + acc) 0 (map (rename ρ) l) =
    foldr (fun x acc => size_exp x + acc) 0 l.
Proof.
  intros ρ l.
  induction l as [|x xs IH]; cbn; [reflexivity|].
  now rewrite size_rename, IH.
Qed.


Lemma normalize_is_ANF :
  forall fuel e k anf, (* preANF k -> *)
    normalize_exp fuel e k = Some anf -> ANF anf.
Proof.
  induction fuel using lt_wf_ind. rename H into IHfuel.
  destruct fuel; intros * (* Hpre *) H; simpl in H. congruence.
  destruct e; simpl in H; try congruence.
  * destruct e; simpl in H; try congruence.
    all: eapply IHfuel in H; [assumption| lia (* | by constructor *)].
  * destruct v; simpl in H; try congruence.
    (* The following technique is repeated for almost all values: ("-" bullets) *)
    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l0.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VLit l]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VLit l]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l0.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VLit l]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VLit l]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].
    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VPid p]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VPid p]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VPid p]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VPid p]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].
    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VVar n]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VVar n]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VVar n]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VVar n]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].


    - (* VFun!!! *)
      destruct normalize_exp eqn:Hexp0 in H; simpl in H; inv H.
      apply IHfuel in Hexp0. 2: lia.
      rename H1 into H.
      destruct fuel; simpl in H; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VFun vl e0]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VFun vl e0]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VFun vl e0]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VFun vl e0]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].



    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VNil]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VNil]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VNil]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VNil]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].
    - destruct fuel; simpl in *; try congruence.
      destruct k; simpl in *. 2: destruct f.
      + inv H. constructor.
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_app _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_app _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VCons v1 v2]).
                apply anf_app. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VCons v1 v2]); apply anf_let_app |lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        constructor. (* inv Hpre. *) apply IHfuel in Hexp; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp1 in H at 2; simpl in H; inv H.
        destruct normalize_exp eqn:Hexp2 in H1; simpl in H1; inv H1.
        (* inv Hpre. *)
        constructor.
          apply IHfuel in Hexp1; [assumption|lia(* |assumption *)].
          apply IHfuel in Hexp2; [assumption|lia(* |assumption *)].
      + destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
        apply IHfuel in Hexp; [assumption|lia].
      + unfold introduce_let in H.
        destruct k;inv H.
        1: { apply anf_val. }
        destruct f.
        all: destruct normalize_exp eqn:Hexp in H1; inv H1;
            apply IHfuel in Hexp; [ repeat constructor; assumption |lia].
      + destruct l.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { by epose proof anf_bif _ []. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [by epose proof anf_let_bif _ [] _ Hexp|lia].
        ** apply IHfuel in H; [assumption | lia ].
      + destruct l2.
        ** unfold introduce_let in H.
           destruct k;inv H.
           1: { rewrite <- map_app with (l' := [VCons v1 v2]).
                apply anf_bif. }
           destruct f.
           all: destruct normalize_exp eqn:Hexp in H1; inv H1;
                apply IHfuel in Hexp; [ by rewrite <- map_app with (l' := [VCons v1 v2]); apply anf_let_bif |lia].
        ** apply IHfuel in H; [assumption | lia ].
Qed.

