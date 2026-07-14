From CoreErlang.Subst Require Export Semantics CIU.
From stdpp Require Export base list.

Print Exp.

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


Definition normalize_name (f : (Exp -> Exp) -> Exp) (k : Exp -> Exp) : Exp :=
  f (fun e' => if is_value e' then k e' else ELet e' (k (VVar 0))).

Fixpoint normalize (e : Exp) (k : Exp -> Exp) {struct e} : Exp :=
match e with
| VVal (VFun vl e) => k (VVal (VFun vl (normalize e id)))
| VVal (VCons e1 e2) => k e (* TODO: might be wrong *)
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


















