(*** migrated ExpManipulation.v: adapt rename/subst to new Exp/Val/NonVal split *)

Require Export ExpSyntax
               Stdlib.Structures.OrderedType.

Import ListNotations.

Definition composition {A B C} (f : A -> B) (g : B -> C) : A -> C := fun x => g (f x).

Notation "f >>> g" := (composition f g)
  (at level 56, left associativity).

Definition Renaming : Type := nat -> nat.

Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

Notation uprenn := (iterate upren).

(* Renaming: mutual over Exp, Val, NonVal *)
Fixpoint rename (ρ : Renaming) (e : Exp) : Exp :=
  match e with
  | VVal v => VVal (rename_val ρ v)
  | EExp nv => EExp (rename_nonval ρ nv)
  end
with rename_val (ρ : Renaming) (v : Val) : Val :=
  match v with
  | VLit l => VLit l
  | VPid p => VPid p
  | VVar n => VVar (ρ n)
  | VFun vl e => VFun vl (rename (uprenn (S vl) ρ) e)
  | VNil => VNil
  | VCons v1 v2 => VCons (rename_val ρ v1) (rename_val ρ v2)
  end
with rename_nonval (ρ : Renaming) (nv : NonVal) : NonVal :=
  match nv with
  | EApp e l => EApp (rename ρ e) (map (rename ρ) l)
  | ELet e1 e2 => ELet (rename ρ e1) (rename (upren ρ) e2)
  | ECase e1 p e2 e3 => ECase (rename ρ e1) p (rename (uprenn (pat_vars p) ρ) e2) (rename ρ e3)
  | ECons e1 e2 => ECons (rename ρ e1) (rename ρ e2)
  | EBIF e l => EBIF (rename ρ e) (map (rename ρ) l)
  | EReceive l => EReceive (map (fun '(p, v) => (p, rename (uprenn (pat_vars p) ρ) v)) l)
  end.

Definition Substitution := nat -> Val + nat.
(** identity elements for shifting *)

Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution :=
  fun s =>
    match ξ s with
    | inl v => inl (rename_val (fun n => S n) v)
    | inr num => inr (S num)
    end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).

(* Substitution: mutual over Exp, Val, NonVal. Substitutions map variable indices to values. *)
Fixpoint subst (ξ : Substitution) (e : Exp) : Exp :=
  match e with
  | VVal v => VVal (subst_val ξ v)
  | EExp nv => EExp (subst_nonval ξ nv)
  end
with subst_val (ξ : Substitution) (v : Val) : Val :=
  match v with
  | VLit l => VLit l
  | VPid p => VPid p
  | VVar n => match ξ n with
              | inl v' => v'
              | inr num => VVar num
              end
  | VFun vl e => VFun vl (subst (upn (S vl) ξ) e)
  | VNil => VNil
  | VCons v1 v2 => VCons (subst_val ξ v1) (subst_val ξ v2)
  end
with subst_nonval (ξ : Substitution) (nv : NonVal) : NonVal :=
  match nv with
  | EApp e l => EApp (subst ξ e) (map (subst ξ) l)
  | ELet e1 e2 => ELet (subst ξ e1) (subst (up_subst ξ) e2)
  | ECase e1 p e2 e3 => ECase (subst ξ e1) p (subst (upn (pat_vars p) ξ) e2) (subst ξ e3)
  | ECons e1 e2 => ECons (subst ξ e1) (subst ξ e2)
  | EBIF e l => EBIF (subst ξ e) (map (subst ξ) l)
  | EReceive l => EReceive (map (fun '(p, v) => (p, subst (upn (pat_vars p) ξ) v)) l)
  end.

Definition scons {X : Type} (s : X) (σ : nat -> X) (x : nat) : X :=
  match x with 
  | S y => σ y
  | _ => s
  end.
Notation "s .: σ" := (scons (inl s) σ) (at level 55, σ at level 56, right associativity).
Notation "s .:: σ" := (scons s σ) (at level 55, σ at level 56, right associativity).
Notation "s .[ σ ]" := (subst σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).
Notation "s .[ t /]" := (subst (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]").
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons (t1) (scons (t2) .. (scons (tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']' ").


Notation "s .ₙ[ σ ]" := (subst_nonval σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .ₙ[ σ ]" ).
Notation "s .ₙ[ t /]" := (subst_nonval (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .ₙ[ t /]").
Notation "s .ₙ[ t1 , t2 , .. , tn /]" :=
  (subst_nonval (scons (t1) (scons (t2) .. (scons (tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .ₙ[ t1 , '/' t2 , '/' .. , '/' tn /] ']' ").

Notation "s .ᵥ[ σ ]" := (subst_val σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .ᵥ[ σ ]" ).
Notation "s .ᵥ[ t /]" := (subst_val (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .ᵥ[ t /]").
Notation "s .ᵥ[ t1 , t2 , .. , tn /]" :=
  (subst_val (scons (t1) (scons (t2) .. (scons (tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .ᵥ[ t1 , '/' t2 , '/' .. , '/' tn /] ']' ").

Definition list_subst (l : list Val) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

Open Scope Z_scope.
(** Tests: retained from original file; they may need adjustment after migration. *)
Goal (inc 1).[VLit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (inc 1).[VLit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (VVar 0) [˝VVar 0; °ELet (VVar 0) (VVar 0)]).[VLit 0/]
  = (EApp (VLit 0) [˝VLit 0; °ELet (VLit 0) (VVar 0)]). Proof. reflexivity. Qed.

Compute (VLit 0 .: VLit 0 .: idsubst) 3.

Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl v => inl (subst_val η v)
    | inr n   => η n
    end.

Ltac fold_upn :=
match goal with
| |- context G [up_subst (upn ?n ?ξ)] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) by auto
| |- context G [upren (uprenn ?n ?ξ)] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) by auto
end.

Ltac fold_upn_hyp :=
match goal with
| [ H : context G [up_subst (upn ?n ?ξ)] |- _ ] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) in H by auto
| [ H : context G [upren (uprenn ?n ?ξ)] |- _ ] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) in H by auto
end.

Definition ren (ρ : Renaming) : Substitution :=
  fun x => inr (ρ x).

Theorem ren_up ρ :
  ren (upren ρ) = up_subst (ren ρ).
Proof.
  extensionality x. unfold ren, upren, up_subst.
  destruct x; reflexivity.
Qed.

Corollary renn_up : forall n ρ,
  ren (uprenn n ρ) = upn n (ren ρ).
Proof.
  induction n; intros; try reflexivity.
  cbn. rewrite ren_up. rewrite IHn. auto.
Qed.

Theorem Private_renaming_is_subst : (forall e ρ,
  rename ρ e = e.[ren ρ]) /\ (forall e ρ,
  rename_nonval ρ e = e.ₙ[ren ρ]) /\ (forall e ρ,
  rename_val ρ e = e.ᵥ[ren ρ]).
Proof.
  apply Exp_full_ind with
    (Q := fun l => forall ρ, Forall (fun e => rename ρ e = e.[ren ρ]) l)
    (W := fun l => forall ρ, Forall (fun '(p,e) => rename ρ e = e.[ren ρ]) l);
  intros; cbn; try reflexivity.
  * by rewrite H.
  * by rewrite H.
  * by rewrite H, ren_up, renn_up.
  * rewrite H. erewrite map_ext_Forall. reflexivity. by auto.
  * rewrite H. rewrite <- ren_up, H0. by auto.
  * rewrite H, H0, <- renn_up, H1. by auto.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * rewrite H. erewrite map_ext_Forall. reflexivity. by auto.
  * erewrite map_ext_Forall. reflexivity.
    induction l; constructor.
    - destruct a. specialize (H (uprenn (pat_vars p) ρ)). inversion H. subst.
      rewrite H2, <- renn_up. reflexivity.
    - apply IHl. intros. specialize (H ρ0). inversion H. by auto.
  * constructor.
  * constructor; auto.
  * constructor.
  * constructor; auto.
Qed.

Corollary renaming_is_subst : (forall e ρ,
  rename ρ e = e.[ren ρ]).
Proof. by apply Private_renaming_is_subst. Qed.

Corollary renaming_is_subst_nonval : (forall e ρ,
  rename_nonval ρ e = e.ₙ[ren ρ]).
Proof. by apply Private_renaming_is_subst. Qed.

Corollary renaming_is_subst_val : forall e ρ,
  rename_val ρ e = e.ᵥ[ren ρ].
Proof. by apply Private_renaming_is_subst. Qed.

Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

Theorem Private_idrenaming_is_id : (forall e, rename id e = e) /\
  (forall e, rename_nonval id e = e) /\
  (forall e, rename_val id e = e).
Proof.
  apply Exp_full_ind with
   (Q := fun l => Forall (fun e => rename id e = e) l)
   (W := fun l => Forall (fun '(_,e) => rename id e = e) l); intros; cbn; try rewrite idrenaming_upn; try rewrite idrenaming_up; try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try reflexivity.
  4-7: by constructor; auto.
  all: rewrite map_ext_Forall with (g := id); auto; try rewrite map_id; try reflexivity.
  induction l; auto; inversion H; constructor; subst; auto.
  destruct a. rewrite idrenaming_upn, H2. reflexivity.
Qed.

Corollary idrenaming_is_id : (forall e, rename id e = e).
Proof. by apply Private_idrenaming_is_id. Qed.

Corollary idrenaming_is_id_nonval : (forall e, rename_nonval id e = e).
Proof. by apply Private_idrenaming_is_id. Qed.

Corollary idrenaming_is_id_val : (forall e, rename_val id e = e).
Proof. by apply Private_idrenaming_is_id. Qed.

Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.

Theorem Private_idsubst_is_id : (forall e, e.[idsubst] = e) /\ (forall e, e.ₙ[idsubst] = e) /\ (forall e, e.ᵥ[idsubst] = e).
Proof.
  apply Exp_full_ind with (Q := fun l => Forall (fun e => e.[idsubst] = e) l)
                                  (W := fun l => Forall (fun '(_,e) => e.[idsubst] = e) l); intros; cbn; try rewrite idsubst_upn; try rewrite idsubst_up; try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try reflexivity.
  4-7: constructor; auto.
  all: rewrite map_ext_Forall with (g := id); auto; try rewrite map_id; try reflexivity.
  induction l; auto; inversion H; constructor; subst; auto.
  destruct a. rewrite idsubst_upn, H2. reflexivity.
Qed.

Corollary idsubst_is_id : (forall e, e.[idsubst] = e).
Proof. by apply Private_idsubst_is_id. Qed.

Corollary idsubst_is_id_nonval : (forall e, e.ₙ[idsubst] = e).
Proof. by apply Private_idsubst_is_id. Qed.

Corollary idsubst_is_id_val : (forall e, e.ᵥ[idsubst] = e).
Proof. by apply Private_idsubst_is_id. Qed.

Lemma up_get_inl ξ x y:
  ξ x = inl y -> up_subst ξ (S x) = inl (rename_val (fun n => S n) y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

Lemma up_get_inr ξ x y:
  ξ x = inr y -> up_subst ξ (S x) = inr (S y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

Open Scope nat_scope.

Lemma renaming_fold m :
  (fun n => m + n) = iterate (fun x => S x) m.
Proof.
  extensionality x. induction m; cbn; auto.
Qed.

Lemma upren_subst_up : forall σ ξ,
  upren σ >>> up_subst ξ = up_subst (σ >>> ξ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>>".
  destruct x; auto.
Qed.

Corollary uprenn_subst_upn n : forall σ ξ,
  uprenn n σ >>> upn n ξ = upn n (σ >>> ξ).
Proof.
  induction n; intros; auto.
  cbn. rewrite <- IHn, upren_subst_up. auto.
Qed.

Lemma Private_subst_ren :
  (forall e (σ : Renaming) (ξ : Substitution), e.[ren σ].[ξ] = e.[σ >>> ξ]) /\
  (forall e (σ : Renaming) (ξ : Substitution), e.ₙ[ren σ].ₙ[ξ] = e.ₙ[σ >>> ξ]) /\
  (forall e (σ : Renaming) (ξ : Substitution), e.ᵥ[ren σ].ᵥ[ξ] = e.ᵥ[σ >>> ξ]).
Proof.
  apply Exp_full_ind with 
    (Q := fun l => forall ξ σ, Forall (fun e => e.[ren σ].[ξ] = e.[σ >>> ξ]) l)
    (W := fun l => forall ξ σ, Forall (fun '(_,e) => e.[ren σ].[ξ] = e.[σ >>> ξ]) l); simpl; intros; auto.
  * by rewrite H.
  * by rewrite H.
  * rewrite <- renn_up, <- ren_up. rewrite H, upren_subst_up, uprenn_subst_upn. auto.
  * rewrite H. erewrite map_map, map_ext_Forall. reflexivity. auto.
  * rewrite <- ren_up, H, H0, upren_subst_up. auto.
  * now rewrite H, H1, <- renn_up, H0, uprenn_subst_upn.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * rewrite H. erewrite map_map, map_ext_Forall. reflexivity. auto.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (H _ _). inversion H0. subst.
      rewrite <- renn_up, H3, uprenn_subst_upn. reflexivity.
    - apply IHl. intros. specialize (H ξ0 σ0). inversion H. auto.
Qed.

Corollary subst_ren :
  (forall e (σ : Renaming) (ξ : Substitution), e.[ren σ].[ξ] = e.[σ >>> ξ]).
Proof. by apply Private_subst_ren. Qed.

Corollary subst_ren_nonval :
  (forall e (σ : Renaming) (ξ : Substitution), e.ₙ[ren σ].ₙ[ξ] = e.ₙ[σ >>> ξ]).
Proof. by apply Private_subst_ren. Qed.

Corollary subst_ren_val :
  (forall e (σ : Renaming) (ξ : Substitution), e.ᵥ[ren σ].ᵥ[ξ] = e.ᵥ[σ >>> ξ]).
Proof. by apply Private_subst_ren. Qed.

Notation "σ >> ξ" := (substcomp σ ξ) (at level 56, left associativity).

Theorem upren_comp : forall σ ρ,
  upren σ >>> upren ρ = upren (σ >>> ρ).
Proof.
  intros. unfold upren, ">>>". extensionality n. destruct n; auto.
Qed.

Corollary uprenn_comp : forall n σ ρ,
  uprenn n σ >>> uprenn n ρ = uprenn n (σ >>> ρ).
Proof.
  induction n; intros; auto. simpl. rewrite upren_comp, IHn. auto.
Qed.

Theorem Private_rename_up : (forall e n σ ρ,
  rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) /\
  (forall e n σ ρ,
  rename_nonval (uprenn n σ) (rename_nonval (uprenn n ρ) e) = rename_nonval (uprenn n (ρ >>> σ)) e) /\
  (forall e n σ ρ,
  rename_val (uprenn n σ) (rename_val (uprenn n ρ) e) = rename_val (uprenn n (ρ >>> σ)) e).
Proof.
  apply Exp_full_ind with
    (Q := fun l => forall n σ ρ, Forall (fun e => rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) l)
    (W := fun l => forall n σ ρ, Forall (fun '(_,e) => rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) l);
  intros; simpl; auto.
  * by rewrite H.
  * by rewrite H.
  * rewrite <- uprenn_comp. reflexivity.
  * repeat fold_upn. rewrite H, uprenn_comp. auto.
  * erewrite H, map_map, map_ext_Forall. reflexivity. auto.
  * rewrite H. do 2 fold_upn. rewrite H0. auto.
  * now rewrite H, H0, H1, <- uprenn_comp.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * erewrite H, map_map, map_ext_Forall. reflexivity. auto.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (H _ _ _). inversion H0. subst.
      rewrite <- uprenn_comp, H3. reflexivity.
    - apply IHl. intros. epose proof (H _ _ _). inversion H0. eauto.
Qed.

Corollary rename_up : (forall e n σ ρ,
  rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e).
Proof. by apply Private_rename_up. Qed.

Corollary rename_up_nonval : (forall e n σ ρ,
  rename_nonval (uprenn n σ) (rename_nonval (uprenn n ρ) e) = rename_nonval (uprenn n (ρ >>> σ)) e).
Proof. by apply Private_rename_up. Qed.

Corollary rename_up_val : (forall e n σ ρ,
  rename_val (uprenn n σ) (rename_val (uprenn n ρ) e) = rename_val (uprenn n (ρ >>> σ)) e).
Proof. by apply Private_rename_up. Qed.

Theorem Private_rename_comp :
  (forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e) /\
  (forall e σ ρ, rename_nonval σ (rename_nonval ρ e) = rename_nonval (ρ >>> σ) e) /\
  (forall e σ ρ, rename_val σ (rename_val ρ e) = rename_val (ρ >>> σ) e).
Proof.
  apply Exp_full_ind with 
    (Q := fun l => forall σ ρ, Forall (fun e => rename σ (rename ρ e) = rename (ρ >>> σ) e) l)
    (W := fun l => forall σ ρ, Forall (fun '(_,e) => rename σ (rename ρ e) = rename (ρ >>> σ) e) l); intros; auto; cbn.
  * by rewrite H.
  * by rewrite H.
  * do 3 fold_upn. now rewrite rename_up.
  * now erewrite H, map_map, map_ext_Forall.
  * now rewrite H, H0, upren_comp.
  * now rewrite H, H1, rename_up.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * now erewrite H, map_map, map_ext_Forall.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (H _ _). inversion H0. subst.
      rewrite <- uprenn_comp, H3. reflexivity.
    - apply IHl. intros. epose proof (H _ _). inversion H0. eauto.
Qed.

Corollary rename_comp :
  (forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e).
Proof. by apply Private_rename_comp. Qed.

Corollary rename_comp_nonval :
  (forall e σ ρ, rename_nonval σ (rename_nonval ρ e) = rename_nonval (ρ >>> σ) e).
Proof. by apply Private_rename_comp. Qed.

Corollary rename_comp_val :
  (forall e σ ρ, rename_val σ (rename_val ρ e) = rename_val (ρ >>> σ) e).
Proof. by apply Private_rename_comp. Qed.

Lemma subst_up_upren : forall σ ξ,
  up_subst ξ >> ren (upren σ) = up_subst (ξ >> ren σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  rewrite <- renaming_is_subst_val, <- renaming_is_subst_val. f_equiv.
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  rewrite rename_comp_val, rename_comp_val. f_equiv.
Qed.

Lemma subst_upn_uprenn : forall n σ ξ,
  upn n ξ >> ren (uprenn n σ) = upn n (ξ >> ren σ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.

Lemma Private_ren_subst : (forall e ξ σ, e.[ξ].[ren σ] = e.[ξ >> ren σ]) /\
  (forall e ξ σ, e.ₙ[ξ].ₙ[ren σ] = e.ₙ[ξ >> ren σ]) /\
  (forall e ξ σ, e.ᵥ[ξ].ᵥ[ren σ] = e.ᵥ[ξ >> ren σ]).
Proof.
  apply Exp_full_ind
    with (Q := fun l => forall ξ σ, Forall (fun e => e.[ξ].[ren σ] = e.[ξ >> ren σ]) l)
         (W := fun l => forall ξ σ, Forall (fun '(_,e) => e.[ξ].[ren σ] = e.[ξ >> ren σ]) l);
  simpl; intros; auto.
  * by rewrite H.
  * by rewrite H.
  * unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * do 3 fold_upn. now rewrite <- renn_up, <- subst_upn_uprenn, H.
  * now erewrite H, map_map, map_ext_Forall.
  * now rewrite <- ren_up, <- subst_up_upren, H, H0.
  * now rewrite H, <- renn_up, <- subst_upn_uprenn, H0, H1.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * now erewrite H, map_map, map_ext_Forall.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (H _ _). inversion H0. subst.
      rewrite <- renn_up, <- subst_upn_uprenn, H3. reflexivity.
    - apply IHl. intros. epose proof (H _ _). inversion H0. eauto.
Qed.

Corollary ren_subst : (forall e ξ σ, e.[ξ].[ren σ] = e.[ξ >> ren σ]).
Proof. by apply Private_ren_subst. Qed.

Corollary ren_subst_nonval : (forall e ξ σ, e.ₙ[ξ].ₙ[ren σ] = e.ₙ[ξ >> ren σ]).
Proof. by apply Private_ren_subst. Qed.

Corollary ren_subst_val : (forall e ξ σ, e.ᵥ[ξ].ᵥ[ren σ] = e.ᵥ[ξ >> ren σ]).
Proof. by apply Private_ren_subst. Qed.

Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (ξ x) eqn:P; auto.
  do 2 rewrite renaming_is_subst_val. rewrite ren_subst_val, subst_ren_val.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold ">>>", ">>", up_subst, shift. destruct (η n) eqn:P0; auto.
  rewrite renaming_is_subst_val. auto.
Qed.

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

Lemma Private_subst_comp : (forall e ξ η, e.[ξ].[η] = e.[ξ >> η]) /\
  (forall e ξ η, e.ₙ[ξ].ₙ[η] = e.ₙ[ξ >> η]) /\
  (forall e ξ η, e.ᵥ[ξ].ᵥ[η] = e.ᵥ[ξ >> η]).
Proof.
  apply Exp_full_ind with 
    (Q := fun l => forall ξ η, Forall (fun e => e.[ξ].[η] = e.[ξ >> η]) l)
    (W := fun l => forall ξ η, Forall (fun '(_,e) => e.[ξ].[η] = e.[ξ >> η]) l); simpl; intros; auto.
  * by rewrite H.
  * by rewrite H.
  * unfold ">>". break_match_goal; auto.
  * do 3 fold_upn. now rewrite H, upn_comp.
  * now erewrite H, map_map, map_ext_Forall.
  * now rewrite H, H0, up_comp.
  * now rewrite H, H0, upn_comp, H1.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * now erewrite H, map_map, map_ext_Forall.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (H _ _). inversion H0. subst.
      rewrite H3, upn_comp. reflexivity.
    - apply IHl. intros. epose proof (H _ _). inversion H0. eauto.
Qed.

Corollary subst_comp : (forall e ξ η, e.[ξ].[η] = e.[ξ >> η]).
Proof. by apply Private_subst_comp. Qed.

Corollary subst_comp_nonval : (forall e ξ η, e.ₙ[ξ].ₙ[η] = e.ₙ[ξ >> η]).
Proof. by apply Private_subst_comp. Qed.

Corollary subst_comp_val : (forall e ξ η, e.ᵥ[ξ].ᵥ[η] = e.ᵥ[ξ >> η]).
Proof. by apply Private_subst_comp. Qed.

Corollary rename_subst_core : forall e v,
  (rename (fun n : nat => S n) e).[v .:: idsubst] = e.
Proof.
  intros.
  rewrite renaming_is_subst, subst_comp. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id. reflexivity.
Qed.

Corollary rename_subst_core_val : forall e v ξ,
  (rename_val (fun n : nat => S n) e).ᵥ[v .:: ξ] = e.ᵥ[ξ].
Proof.
  intros.
  rewrite renaming_is_subst_val, subst_comp_val. cbn.
  unfold substcomp, ren. cbn. reflexivity.
Qed.

Corollary rename_subst_core_val_idsubst : forall e v,
  (rename_val (fun n : nat => S n) e).ᵥ[v .:: idsubst] = e.
Proof.
  intros. rewrite rename_subst_core_val. by rewrite idsubst_is_id_val.
Qed.

Corollary rename_subst_core_nonval : forall e v,
  (rename_nonval (fun n : nat => S n) e).ₙ[v .:: idsubst] = e.
Proof.
  intros.
  rewrite renaming_is_subst_nonval, subst_comp_nonval. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id_nonval. reflexivity.
Qed.

Corollary rename_subst : forall e v,
  (rename (fun n : nat => S n) e).[v/] = e.
Proof.
  intros. apply rename_subst_core.
Qed.

Corollary rename_subst_val : forall e v,
  (rename_val (fun n : nat => S n) e).ᵥ[v/] = e.
Proof.
  intros. apply rename_subst_core_val_idsubst.
Qed.

Corollary rename_subst_nonval : forall e v,
  (rename_nonval (fun n : nat => S n) e).ₙ[v/] = e.
Proof.
  intros. apply rename_subst_core_nonval.
Qed.


Lemma scons_substcomp_core v ξ η :
  (v .:: ξ) >> η = match v with 
                   | inl exp => inl (exp.ᵥ[η])
                   | inr n => η n
                   end .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.

Lemma scons_substcomp v ξ η :
  (v .: ξ) >> η = v.ᵥ[η] .: (ξ >> η).
Proof.
  apply scons_substcomp_core.
Qed.

Lemma scons_substcomp_list ξ η vals :
  (list_subst vals ξ) >> η = list_subst (map (subst_val η) vals) (ξ >> η).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.

Lemma substcomp_scons_core v ξ η :
  up_subst ξ >> v .:: η = v .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  rewrite renaming_is_subst_val, subst_comp_val. f_equiv.
Qed.

Lemma substcomp_scons v ξ η :
  up_subst ξ >> v .: η = v .: (ξ >> η).
Proof.
  apply substcomp_scons_core.
Qed.

Corollary substcomp_list l ξ η :
  upn (length l) ξ >> list_subst l η = list_subst l (ξ >> η).
Proof.
  induction l; simpl; auto.
  * now rewrite substcomp_scons, IHl.
Qed.

Theorem subst_extend_core : forall ξ η v,
  (up_subst ξ) >> (v .:: η) = v .:: (ξ >> η).
Proof.
  intros. unfold substcomp. extensionality x. destruct x; auto.
  cbn. break_match_goal.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs.
    rewrite rename_subst_core_val. auto.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. cbn. reflexivity.
Qed.

Corollary subst_extend : forall ξ η v,
  (up_subst ξ) >> (v .: η) = v .: (ξ >> η).
Proof.
  intros. apply subst_extend_core.
Qed.

Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals (VLit (Int 0))).
Proof.
  induction n; intros; destruct vals.
  * inversion H.
  * simpl. auto.
  * inversion H.
  * simpl in H.
    apply Nat.succ_lt_mono in H. eapply IHn in H. simpl. exact H.
Qed.

Theorem list_subst_ge : forall n vals ξ, n >= length vals ->
  list_subst vals ξ n = ξ (n - length vals).
Proof.
  induction n; intros; destruct vals.
  * simpl. auto.
  * inversion H.
  * cbn. auto.
  * simpl in H. apply le_S_n in H. eapply IHn in H. simpl. exact H.
Qed.

Corollary list_subst_get_possibilities : forall n vals ξ,
  list_subst vals ξ n = inl (nth n vals (VLit (Int 0))) /\ n < length vals
\/
  list_subst vals ξ n = ξ (n - length vals) /\ n >= length vals.
Proof.
  intros. pose (Nat.lt_decidable n (length vals)). destruct d.
  * left. split. now apply list_subst_lt. auto.
  * right. split. apply list_subst_ge. lia. lia.
Qed.

Lemma substcomp_id_r :
  forall ξ, ξ >> idsubst = ξ.
Proof.
  unfold ">>". intros. extensionality x.
  break_match_goal; auto. rewrite idsubst_is_id_val. auto.
Qed.

Lemma substcomp_id_l :
  forall ξ, idsubst >> ξ = ξ.
Proof.
  unfold ">>", idsubst. intros. extensionality x. auto.
Qed.

Theorem subst_extend_id : forall ξ v,
  (up_subst ξ) >> (v .: idsubst) = v .: ξ.
Proof.
  intros. rewrite subst_extend. by rewrite substcomp_id_r.
Qed.

Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (upn n ξ) >> (list_subst vals idsubst) = list_subst vals ξ.
Proof.
  induction n; intros.
  * apply length_zero_iff_nil in H. subst. cbn. unfold substcomp. extensionality x.
    break_match_goal; try rewrite idsubst_is_id_val; try reflexivity.
  * simpl. apply eq_sym in H as H'. apply element_exist in H'. destruct H', H0. subst.
    simpl. rewrite substcomp_scons. rewrite IHn; auto.
Qed.

Lemma subst_ren_scons : forall (ξ : Substitution) e,
  ξ 0 = inl e ->
  (e .: (fun n : nat => n + 1) >>> ξ) = ξ.
Proof.
  intros. extensionality x. unfold ">>>", scons. destruct x; auto.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma ren_up_subst :
  forall ξ,
    ren (fun n => S n) >> up_subst ξ = ξ >> ren (fun n => S n).
Proof.
  intros. extensionality x; cbn.
  unfold shift. unfold ">>".
  break_match_goal; cbn.
  now rewrite <- renaming_is_subst_val.
  reflexivity.
Qed.

Lemma ren_scons :
  forall ξ f, forall x, ren (fun n => S (f n)) >> x .: ξ = ren (fun n => f n) >> ξ.
Proof.
  intros.
  extensionality k. cbn. auto.
Qed.

Lemma rename_upn_list_subst :
  forall m ξ vals, length vals = m ->
    ren (fun n => m + n) >> (upn m ξ >> list_subst vals idsubst) = ξ.
Proof.
  intros.
  rewrite (subst_list_extend m ξ vals H).
  generalize dependent vals. induction m; intros; cbn.
  - replace (ren (fun n => n)) with idsubst by auto. apply length_zero_iff_nil in H.
    subst. cbn. now rewrite substcomp_id_l.
  - assert (length vals = S m) by auto.
    apply eq_sym, element_exist in H as [x0 [xs H1]]. subst. inversion H0.
    replace (list_subst (x0 :: xs) ξ) with (x0 .: list_subst xs ξ) by auto.
    specialize (IHm xs H1).
    erewrite H1, ren_scons; eauto.
Qed.

Ltac fold_list_subst :=
match goal with
| |- context G [?x .: list_subst ?xs ?ξ] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) by auto
end.

Ltac fold_list_subst_hyp :=
match goal with
| [H: context G [?x .: list_subst ?xs ?ξ] |- _] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) in H by auto
end.

Lemma substcomp_assoc :
  forall ξ σ η, (ξ >> σ) >> η = ξ >> (σ >> η).
Proof.
  intros. extensionality x. unfold ">>".
  destruct (ξ x) eqn:D1; auto.
  rewrite subst_comp_val. reflexivity.
Qed.
