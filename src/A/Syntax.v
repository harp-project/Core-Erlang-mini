From CoreErlang.Subst Require Export Semantics CIU.
From stdpp Require Export base list.


(* Program contexts for the context-based ANF normalizer.  Unlike the
   continuation-based normalizer above, the remaining computation is
   represented explicitly by an [NCtx] frame stack. *)
Inductive NCtx : Set :=
| NCHole
| NCLet (e2 : Exp) (k : NCtx)
(* | NCCase (p : Pat) (e1 e2 : Exp) (k1 k2 : NCtx) *)
| NCCase (p : Pat) (e1 e2 : Exp) (k : NCtx)
| NCApp1 (args : list Exp) (k : NCtx)
| NCApp2 (f : Val) (done : list Val) (todo : list Exp) (k : NCtx)
| NCBIF1 (args : list Exp) (k : NCtx)
| NCBIF2 (f : Val) (done : list Val) (todo : list Exp) (k : NCtx)
| NCCons1 (e1 : Exp) (k : NCtx)
| NCCons2 (e2 : Val) (k : NCtx).

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

Definition plug_fs (Fs : FrameStack) (e : Exp) := fold_right plug_f e Fs.

Definition rename_frame (ρ : Renaming) (f : Frame) : Frame :=
match f with
 | FApp1 l => FApp1 (map (rename ρ) l)
 | FApp2 v l1 l2 => FApp2 (rename_val ρ v) (map (rename_val ρ) l1) (map (rename ρ) l2)
 | FLet e2 => FLet (rename ρ e2)
 | FCase p e2 e3 => FCase p (rename ρ e2) (rename ρ e3)
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


Fixpoint split_list_val (l : list Exp) : list Val * list Exp :=
match l with
| []    => ([], [])
| e::es => match e with
           | VVal v =>
             let '(vals, exps) := split_list_val es in
               (v :: vals, exps)
           | EExp e => ([], EExp e::es)
           end
end.

Definition is_value (e : Exp) : bool :=
match e with
 | EExp e => false
 | VVal v => true
end.

Definition is_comp_value (e : Exp) : bool :=
match e with
 | EExp e =>
   match e with
    | EBIF exp l | EApp exp l => is_value exp && forallb is_value l
    | _ => false
   end   
 | VVal v => true
end.

(* Takewhile needed *)
Definition A_normalize_heat (e : Exp) : option (Frame * Exp) :=
match e with
 | EExp e =>
   match e with
   | EApp exp l =>
     match exp with
     | VVal v1 =>
       let '(vals, exps) := split_list_val l in
         match exps with
         | [] => None
         | e::es => Some (FApp2 v1 vals es, e)
         end
     | _ => Some (FApp1 l, exp)
     end
   | ELet e1 e2 =>
     if is_comp_value e1
     then None
     else Some (FLet e2, e1)
   | ECase e p e1 e2 =>
     if is_value e
     then None
     else Some (FCase p e1 e2, e)
   | ECons e1 e2 =>
     match e2 with
     | VVal v2 => match e1 with
                  | VVal v1 => None
                  | _       => Some (FCons2 v2, e1)
                  end
     | _       => Some (FCons1 e1, e2)
     end
   | EReceive l => None
   | EBIF exp l =>
     match exp with
     | VVal v1 =>
       let '(vals, exps) := split_list_val l in
         match exps with
         | [] => None
         | e::es => Some (FBIF2 v1 vals es, e)
         end
     | _       => Some (FBIF1 l, exp)
     end
  end
 | VVal v => None
end.

(*
Full def, but ill-formed due to split:

Fixpoint A_normalize_heat (ebase : Exp) : option (FrameStack * Exp) :=
match ebase with
 | EExp ee =>
   match ee with
   | EApp exp l =>
     match exp with
     | VVal v1 =>
       let '(vals, exps) := split_list_val l in
         match exps with
         | [] => None
         | e::es =>
            match A_normalize_heat e with
            | None => Some ([FApp2 v1 vals es], e)
            | Some (fs, e') => Some (FApp2 v1 vals es :: fs, e')
            end
         end
     | _       => 
       match A_normalize_heat exp with
        | None => Some ([FApp1 l], exp)
        | Some (fs, e') => Some (FApp1 l :: fs, e')
       end
     end
   | ELet e1 e2 =>
     if is_value e1
     then None
     else match A_normalize_heat e1 with
           | None => Some ([FLet e2], e1)
           | Some (fs, e') => Some (FLet e2 :: fs, e')
          end
   | ECase e p e1 e2 =>
     if is_value e
     then None
     else match A_normalize_heat e with
           | None => Some ([FCase p e1 e2], e)
           | Some (fs, e') => Some (FCase p e1 e2 :: fs, e')
          end
   | ECons e1 e2 =>
     match e2 with
     | VVal v2 => match e1 with
                  | VVal v1 => None
                  | _       =>
                    match A_normalize_heat e1 with
                     | None => Some ([FCons2 v2], e1)
                     | Some (fs, e') => Some (FCons2 v2 :: fs, e')
                    end
                  end
     | _       => match A_normalize_heat e1 with
                   | None => Some ([FCons1 e1], e2)
                   | Some (fs, e') => Some (FCons1 e1 :: fs, e')
                  end
     end
   | EReceive l => None
   | EBIF exp l =>
     match exp with
     | VVal v1 =>
       let '(vals, exps) := split_list_val l in
         match exps with
         | [] => None
         | e::es =>
            match A_normalize_heat e with
            | None => Some ([FBIF2 v1 vals es], e)
            | Some (fs, e') => Some (FBIF2 v1 vals es :: fs, e')
            end
         end
     | _       => 
       match A_normalize_heat exp with
        | None => Some ([FBIF1 l], exp)
        | Some (fs, e') => Some (FBIF1 l :: fs, e')
       end
     end
  end
 | VVal v => None
end.
*)

Fixpoint A_normalize_heat_rec (iters : nat) (e : Exp) : option (FrameStack * Exp) :=
match iters with
| 0 => None
| S iters' =>
  match A_normalize_heat e with
  | None => Some ([], e)
  | Some (F, e') =>
    match A_normalize_heat_rec iters' e' with
    | None => None
    | Some (Fs, e'') => Some (F::Fs, e'')
    end
  end
end.
(* TODO: normalize_heat_rec always correctly terminates - see commented def,
   which would be correct, if we inlined split.
 *)


(* TODO: side conds - renamings
   IN the nameless presentation, the scope order gets reversed by this
   transformation - therefore, renamings have to be applied to ensure the
   correct binding structure *)
Definition A_normalize_reduce (Fs : FrameStack) (e : Exp) : option Exp :=
match e with
 | EExp (ELet e1 e2) =>
   (* e2 should not be touched, because it is placed in a position where
      a closed expression is expected -> we "close it" by the "outer" let
      Fs does not need to be touched because it is closed -> bindings 
      cannot get tangled up *)
   Some (°ELet e1 (plug_fs Fs e2))
 | EExp (ECase e p e1 e2) =>
   if is_value e
   (* The same applies here *)
   then Some (°ECase e p (plug_fs Fs e1) (plug_fs Fs e2))
   else None
 (* We do not need renaming in the following cases either because
    we expect that the frame stack is closed, therefore, it does
    not contain a dangling 0 index, so we can safely put it inside
    with an outer "let" binding it *)
 | EExp (EApp exp l) =>
   if is_value exp then if forallb is_value l
   then Some (°ELet e (plug_fs Fs (VVar 0)))
   else None
   else None
 | EExp (EBIF exp l) =>
   if is_value exp then if forallb is_value l
   then Some (°ELet e (plug_fs Fs (VVar 0)))
   else None
   else None
 | EExp (ECons e1 e2) =>
   if is_value e1 then if is_value e2
   then Some (°ELet e (plug_fs Fs (VVar 0)))
   else None
   else None
 | _ => None
end.

(* Better question: normalize heat + normalize reduce repeatedly iterated is OK? *)

Definition A_normalize_step (iters : nat) (e : Exp) : option Exp :=
  match A_normalize_heat_rec iters e with
  | Some ([], e) => None
  | Some (fs, e) => A_normalize_reduce fs e
  | None => None
  end.

Fixpoint A_normalize (iters : nat) (iters2 : nat) (e : Exp) : option Exp :=
match iters with
| 0 => None
| S iters' =>
  match (A_normalize_step iters2 e) with
  | Some exp => A_normalize iters' iters2 exp
  | None => Some e (* not OK, if iters2 is too low *)
  end
end.


Open Scope string_scope.
Definition ex1 : NonVal :=
  ELet (VLit 0%Z) (EBIF (VLit "+"%string) [˝VLit 3%Z; ˝VVar 0]).
Definition fs1 : FrameStack := [FLet (VVar 0)].

Compute plug_fs fs1 ex1.
Compute A_normalize_reduce fs1 ex1.


Compute A_normalize_heat_rec 100 (plug_fs fs1 ex1).
Compute A_normalize_reduce [(FLet (˝ VVar 0))] (ELet (VLit 0%Z)
               (EBIF (˝VLit "+")
                  (cons (˝VLit 3%Z) (cons (˝VVar 0) nil)))).

Compute A_normalize_heat_rec 100 (ELet (VLit 0%Z)
            (ELet
               (EBIF (VLit "+")
                  (cons (˝VLit 3%Z) (cons (˝VVar 0) nil)))
               (VVar 0))).

Compute A_normalize 100 100 (plug_fs fs1 ex1).













(* Reserved Notation "⟨ Fs , e ⟩ '-A->' ⟨ Fs' , e' ⟩" (at level 60).
Inductive A_normalize : FrameStack -> Exp -> Exp -> Prop :=

(* actual rules *)
| norm_let :
  ⟨Fs, ELet e1 e2⟩ -A-> 

(* construct evaluation context *)

where "⟨ Fs , e ⟩ '-A->' e'" := (A_normalize Fs e e'). *)

(* Inductive Conf : Set :=
| ELet  (e1 : Comp) (e2 : Conf)
| ECase (e : Val) (p : Pat) (e1 e2 : Conf)
| EComp (n : Comp)

with Comp : Set :=
| EApp (v : Val) (l : list Val)
| EBIF (v : Val) (l : list Val)
| EVal (v : Val)

with Val : Set :=
| VLit   (l : Lit)
| VVar   (n : nat)
| VNil
| VCons (v1 v2 : Val)
| VClos (Γ : list Val) (vl : nat) (e : Conf). *)


(* Inductive NCtx : Set :=
| CBox
| CLet (e2 : Exp)
| CCase (p : Pat) (e1 e2 : Exp)
| CCons (c1 c2 : NCtx)
| CApp (c : NCtx) (l : list NCtx)
| CBIF (c : NCtx) (l : list NCtx).


Axiom applyCtx : NCtx -> Exp -> Exp.
Axiom applyCCtx : NCtx -> NCtx -> NCtx.

Definition normalize_name (f : NCtx -> Exp) (k : NCtx) : Exp. Admitted.
  (* f (fun e' => if is_value e' then applyCtx k e' else ELet e' (applyCtx k (VVar 0))). *)

Fixpoint normalize (e : Exp) (k : NCtx) {struct e} : Exp :=
match e with
| VVal (VFun vl e) => applyCtx k (VVal (VFun vl (normalize e id)))
| VVal (VCons e1 e2) => applyCtx k e (* TODO: might be wrong *)
| VVal v => applyCtx k (VVal v)
| EExp (ELet e1 e2) => normalize e1 (CLet1 (normalize e2 k))
| EExp (ECase e p e1 e2) => normalize_name (normalize e) (applyCCtx k (CCase1 p (normalize e1 k) (normalize e2 k)))
| EExp (EApp e1 l) => normalize_name (normalize e1) (fun e1' =>
     (fix normalize_name_star (l : list Exp) (k : NCtx) {struct l} : Exp :=
      match l with
      | [] => k []
      | e::es => normalize_name (normalize e) (fun e' => normalize_name_star es (fun es' => k (e'::es')))
      end) l (fun '(l1', l2') => applyCCtx k (CApp2 e1' l1' l2')))
| EExp (EBIF e1 l) => normalize_name (normalize e1) (fun e1' => 
     (fix normalize_name_star (l : list Exp) (k : NCtx) {struct l} : Exp :=
      match l with
      | [] => k []
      | e::es => normalize_name (normalize e) (fun e' => normalize_name_star es (fun es' => k (e'::es')))
      end) l (fun '(l1', l2') => applyCCtx k (CBIF2 e1' l1' l2')))
| EExp (ECons e1 e2) => normalize_name (normalize e2) (applyCCtx k (CCons CBox CBox))

normalize_name (normalize e2)
  (fun e2' => normalize_name (normalize e1) (fun e1' => k (ECons e1' e2')))




(fun e2' => normalize_name (normalize e1) (fun e1' => applyCCtx k (CCons1 e1')))
| EExp (EReceive l) => inf (* TODO option? *)
end.

Definition normalize_term (e : Exp) : Exp := normalize e id. *)










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

Fixpoint rename_nctx (ρ : Renaming) (k : NCtx) : NCtx :=
  match k with
  | NCHole => NCHole
  | NCLet e2 k' =>
      NCLet (rename (upren ρ) e2) (rename_nctx (upren ρ) k')
  (* | NCCase p e1 e2 k1 k2 =>
      NCCase p (rename (uprenn (pat_vars p) ρ) e1) (rename ρ e2)
        (rename_nctx (uprenn (pat_vars p) ρ) k1) (rename_nctx ρ k2) *)
  | NCCase p e1 e2 k =>
      NCCase p (rename (uprenn (pat_vars p) ρ) e1) (rename ρ e2) (rename_nctx ρ k)
  | NCApp1 args k' => NCApp1 (map (rename ρ) args) (rename_nctx ρ k')
  | NCApp2 f done todo k' =>
      NCApp2 (rename_val ρ f) (map (rename_val ρ) done) (map (rename ρ) todo)
        (rename_nctx ρ k')
  | NCBIF1 args k' => NCBIF1 (map (rename ρ) args) (rename_nctx ρ k')
  | NCBIF2 f done todo k' =>
      NCBIF2 (rename_val ρ f) (map (rename_val ρ) done) (map (rename ρ) todo)
        (rename_nctx ρ k')
  | NCCons1 e1 k' => NCCons1 (rename ρ e1) (rename_nctx ρ k')
  | NCCons2 e2 k' => NCCons2 (rename_val ρ e2) (rename_nctx ρ k')
  end.

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

Fixpoint size_nctx (k : NCtx) : nat :=
  match k with
  | NCHole => 0
  | NCLet e2 k' => (size_exp e2 + size_nctx k')
  | NCCase _ e1 e2 k' => (size_exp e1 + size_exp e2 + size_nctx k')
  | NCApp1 args k' =>
    (foldr (fun x acc => size_exp x + acc) 0 args + size_nctx k')
  | NCApp2 f done todo k' =>
    (* S (size_exp f + *)
      (* foldr (fun x acc => size_exp x + acc) 0 done + *)
      foldr (fun x acc => size_exp x + acc) 0 todo + size_nctx k'
  | NCBIF1 args k' =>
    (foldr (fun x acc => size_exp x + acc) 0 args + size_nctx k')
  | NCBIF2 f done todo k' =>
    (* S (size_exp f + *)
      (* foldr (fun x acc => size_exp x + acc) 0 done + *)
      foldr (fun x acc => size_exp x + acc) 0 todo + size_nctx k'
  | NCCons1 e1 k' => (size_exp e1 + size_nctx k')
  | NCCons2 e2 k' => ( (*size_exp e2 +*) size_nctx k')
  end.


Lemma size_rename_exp :
  forall e ρ, size_exp (rename ρ e) = size_exp e.
Proof. Check Exp_ind2.
  (* refine
    (Exp_ind2
       (P := fun e => forall ρ, size_exp (rename ρ e) = size_exp e)
       (PV := fun v => forall ρ, size_val (rename_val ρ v) = size_val v)
       (PN := fun nv => forall ρ, size_exp (EExp (rename_nonval ρ nv)) = size_exp (EExp nv))
       (Q := fun l =>
               forall ρ,
                 foldr (fun x acc => size_exp x + acc) 0 (map (rename ρ) l) =
                 foldr (fun x acc => size_exp x + acc) 0 l)
       (W := fun l =>
               forall ρ,
                 foldr (fun '(p, e) acc => size_exp e + acc) 0
                   (map (fun '(p, v) => (p, rename (uprenn (pat_vars p) ρ) v)) l) =
                 foldr (fun '(p, e) acc => size_exp e + acc) 0 l));
    cbn; intros; try reflexivity.
  - intros ρ. now rewrite H.
  - intros ρ. exact (H ρ).
  - intros ρ. now rewrite H.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H, H0, H1.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H, H0.
  - intros ρ. now rewrite H, H0. *)
Admitted.

Lemma fold_size_exp_rename :
  forall ρ l,
    foldr (fun x acc => size_exp x + acc) 0 (map (rename ρ) l) =
    foldr (fun x acc => size_exp x + acc) 0 l.
Proof.
  intros ρ l.
  induction l as [|x xs IH]; cbn; [reflexivity|].
  now rewrite size_rename_exp, IH.
Qed.

Lemma size_nctx_rename_nctx :
  forall ρ k, size_nctx (rename_nctx ρ k) = size_nctx k.
Proof.
  (* intros ρ k.
  induction k as
    [
    | e2 k' IH
    | p e1 e2 k' IH
    | args k' IH
    | f done todo k' IH
    | args k' IH
    | f done todo k' IH
    | e1 k' IH
    | e2 k' IH
    ]; cbn.
  - reflexivity.
  - now rewrite size_exp_rename, IH.
  - now rewrite size_exp_rename, size_exp_rename, IH.
  - now rewrite fold_size_exp_rename, IH.
  - now rewrite fold_size_exp_rename, IH.
  - now rewrite fold_size_exp_rename, IH.
  - now rewrite fold_size_exp_rename, IH.
  - now rewrite size_exp_rename, IH.
  - exact IH. *)
Admitted.

(* Lemma normalize_total_helper :
    (forall (e : Exp) k, exists fuel, normalize_exp fuel e k <> None) /\
    (forall (e : NonVal) k, exists fuel, normalize_exp fuel e k <> None) /\
    (forall (e : Val) k, exists fuel, normalize_val fuel e k <> None).
Proof.
  apply Exp_full_ind with
      (Q := Forall (fun e => forall k, exists fuel, normalize_exp fuel e k <> None))
      (W := Forall (fun '(_, e) => forall k, exists fuel, normalize_exp fuel e k <> None)); intros.


Admitted. *)
Print NCtx.
(* Inductive preANF : NCtx -> Prop :=
| preANF_hole :
  preANF NCHole

| preANF_let e1 k:
  preANF k
->
  preANF (NCLet e1 k)

| preANF_case p e1 e2 k:
  preANF k
->
  preANF (NCCase p e1 e2 k)

| preANF_app1 l k:
  preANF k
->
  preANF (NCApp1 l k)

| preANF_bif1 l k:
  preANF k
->
  preANF (NCBIF1 l k)

| preANF_app2 f done todo k:
  Forall ANF done -> ANF f -> preANF k
->
  preANF (NCApp2 f done todo k)

| preANF_bif2 f done todo k:
  Forall ANF done -> ANF f -> preANF k
->
  preANF (NCBIF2 f done todo k)

| preANF_cons1 e1 k:
  preANF k
->
  preANF (NCCons1 e1 k)

| preANF_cons2 e2 k:
  ANF e2 -> preANF k
->
  preANF (NCCons2 e2 k). *)

(* Lemma rename_ANF :
  forall e ρ, ANF e -> ANF (rename ρ e).
Proof.

Admitted. *)

(* Lemma rename_preANF :
  forall k ρ, preANF k -> preANF (rename_nctx ρ k).
Proof.

Admitted. *)

(* Lemma Private_introduce_let_ANF k e anf fuel :
  (forall e k anf, preANF k ->
    normalize_exp fuel e k = Some anf -> ANF anf) ->
  preANF k -> ANF e -> introduce_let (normalize_exp fuel) k e = Some anf ->
  ANF anf.
Proof.
  intros * IH Hpre He H.
  unfold introduce_let in H.
  destruct k; inv Hpre.
  * assumption.
  * destruct normalize_exp eqn:Hexp in H; simpl in H; inv H.
    apply IH in Hexp. 2: assumption.
    
  *
  *
  *
  *
  *
  *
  *
Qed. *)

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






















Fixpoint NCtx_to_FrameStack (k : NCtx) : FrameStack :=
match k with
 | NCHole => []
 | NCLet e2 k => FLet e2 :: NCtx_to_FrameStack k
 | NCCase p e1 e2 k => FCase p e1 e2 :: NCtx_to_FrameStack k
 | NCApp1 args k => FApp1 args :: NCtx_to_FrameStack k
 | NCApp2 f done todo k => FApp2 f done todo :: NCtx_to_FrameStack k
 | NCBIF1 args k => FBIF1 args :: NCtx_to_FrameStack k
 | NCBIF2 f done todo k => FBIF2 f done todo :: NCtx_to_FrameStack k
 | NCCons1 e1 k => FCons1 e1 :: NCtx_to_FrameStack k
 | NCCons2 e2 k => FCons2 e2 :: NCtx_to_FrameStack k
end.



Lemma normalize_preserves_semantics :
  ⟨, e⟩ --> ⟨⟩
  normalize_exp fuel e k = Some anf ->
  





Lemma normalize_total_helper :
  (forall e k, normalize_exp (size_exp e + 2* size_nctx k) e k <> None).
Proof.
  intros.
  remember (size_exp e + 2* size_nctx k) as fuel.
  assert (fuel >= size_exp e + 2* size_nctx k) as Hfuel by lia. clear Heqfuel.
  revert e k Hfuel.
  induction fuel using lt_wf_ind; intros e k Hfuel.
  intro. destruct fuel, e; simpl in H0, Hfuel; try lia.
  * destruct e eqn:P.
    - eapply H in H0. assumption. lia. simpl. lia.
    - eapply H in H0. assumption. lia. simpl. lia.
    - eapply H in H0. assumption. lia. simpl. lia.
    - eapply H in H0. assumption. lia. simpl. lia.
    - (* TODO: receive *) admit.
    - eapply H in H0. assumption. lia. simpl. lia.
  * destruct v; simpl in *.
    (* The proofs here should all be the same (except for VClos) *)
    - destruct fuel; simpl in *; try lia.
      destruct k; cbn in *; try congruence.
      + destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
        eapply H in Hexp. assumption. lia. simpl. lia.
      + destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
        2: { eapply H in Hexp. assumption. lia. simpl. lia. }
        destruct (normalize_exp fuel e1) eqn:Hexp2; simpl in H0; try congruence.
        eapply H in Hexp2. assumption. lia. simpl. lia.
      + destruct args; simpl in Hfuel.
        ** unfold introduce_let in H0. destruct k; try congruence.
        (* The proofs here should all be the repetitive *)
           -- destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel. lia.
           -- case_match. by cbn in H1.
              destruct fuel; simpl in *; try lia.
              destruct fuel; simpl in *; try lia.
              destruct (normalize_exp)eqn:Hexp in H0; simpl in H0; try congruence.
              2: {  eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel. lia. }
              
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.


              rewrite size_nctx_rename_nctx, size_rename_exp, size_rename_exp. lia.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
        ** destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
           eapply H in Hexp. assumption. lia. simpl. lia.
      + destruct todo; simpl in Hfuel.
        ** unfold introduce_let in H0. destruct k; try congruence.
        (* The proofs here should all be the repetitive *)
           -- destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel. lia.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
           -- case_match. by cbn in H1.
              destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
              eapply H in Hexp. assumption. lia. simpl. cbn in Hfuel.
              admit.
        ** destruct normalize_exp eqn:Hexp; simpl in H0; try congruence.
           eapply H in Hexp. assumption. lia. simpl. lia.
      (* + 
      +
      +
      +
    - admit.
    - admit.
    - admit.
    - admit.
    - admit. *)
Admitted. *)

(* Corollary normalize_ctx_term_total :
  forall e, exists limit e', normalize_ctx_term e limit = Some e'.
Proof.
  intros e.
  exact (proj1 normalize_total e NCHole).
Qed. *)



