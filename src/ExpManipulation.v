Require Export ExpSyntax
               Coq.Structures.OrderedType.

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


Fixpoint rename (ρ : Renaming) (e : Exp) : Exp :=
match e with
 | ELit l => e
 | EPid p => e
 | EVar n => EVar (ρ n)
 | EFunId n => EFunId (ρ n)
 | EFun vl e => EFun vl (rename (uprenn (S (length vl)) ρ) e)
 | EApp exp l => EApp (rename ρ exp) (map (rename ρ) l)
 | ELet v e1 e2 => ELet v (rename ρ e1) (rename (upren ρ) e2)
 | ELetRec f vl b e => ELetRec f vl (rename (uprenn (1 + length vl) ρ) b) 
                                    (rename (upren ρ) e)
 | EPlus e1 e2 => EPlus (rename ρ e1) (rename ρ e2)
 | ECase e1 p e2 e3 => ECase (rename ρ e1) p (rename (uprenn (pat_vars p) ρ) e2) (rename ρ e3)
 | ECons e1 e2 => ECons (rename ρ e1) (rename ρ e2)
 | ENil => e
 | VCons e1 e2 => VCons (rename ρ e1) (rename ρ e2)
 | ESend p e => ESend p (rename ρ e)
 | EReceive l => EReceive (map (fun '(p, v) => (p, rename (uprenn (pat_vars p) ρ) v)) l)
end.

Definition Substitution := nat -> Exp + nat. (** We need to have the names for the
                                                  identity elements explicitly, because 
                                                  of the shiftings (up, upn) *)
Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (rename (fun n => S n) exp)
  | inr num => inr (S num)
  end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).

Fixpoint subst (ξ : Substitution) (base : Exp) : Exp :=
match base with
 | ELit l => base
 | EPid p => base
 | EVar n => match ξ n with
             | inl exp => exp
             | inr num => EVar num
             end
 | EFunId n => match ξ n with
               | inl exp => exp
               | inr num => EFunId num
               end
 | EFun vl e => EFun vl (subst (upn (S (length vl)) ξ) e)
 | EApp exp l => EApp (subst ξ exp) (map (subst ξ) l)
 | ELet v e1 e2 => ELet v (subst ξ e1) (subst (up_subst ξ) e2)
 | ELetRec f vl b e => ELetRec f vl (subst (upn (1 + length vl) ξ) b)
                                    (subst (up_subst ξ) e)
 | EPlus e1 e2 => EPlus (subst ξ e1) (subst ξ e2)
 | ECase e1 p e2 e3 => ECase (subst ξ e1) p (subst (upn (pat_vars p) ξ) e2) (subst ξ e3)
 | ECons e1 e2 => ECons (subst ξ e1) (subst ξ e2)
 | ENil => base
 | VCons e1 e2 => VCons (subst ξ e1) (subst ξ e2)
 | ESend p e => ESend p (subst ξ e)
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
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").

Definition list_subst (l : list Exp) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

(** Tests: *)
Goal (inc 1).[ELit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (inc 1).[ELit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (EVar 0) [EVar 0; ELet XVar (EVar 0) (EVar 0)]).[ELit 0/]
  = (EApp (ELit 0) [ELit 0; ELet XVar (ELit 0) (EVar 0)]). Proof. reflexivity. Qed.

Compute (ELit 0 .: ELit 0 .: idsubst) 3.

Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl exp => inl (subst η exp)
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

Theorem renaming_is_subst : forall e ρ,
  rename ρ e = e.[ren ρ].
Proof.
  induction e using Exp_ind2 with 
    (Q := fun l => forall ρ, Forall (fun e => rename ρ e = e.[ren ρ]) l)
    (W := fun l => forall ρ, Forall (fun '(p,e) => rename ρ e = e.[ren ρ]) l)
    ; intros; try reflexivity; cbn.
  * rewrite IHe, ren_up, renn_up. auto.
  * rewrite IHe. erewrite map_ext_Forall. reflexivity. auto.
  * rewrite IHe1. rewrite <- ren_up, IHe2. auto.
  * rewrite <- ren_up, <- renn_up, IHe1, IHe2, <- ren_up. auto.
  * rewrite IHe1, IHe2. auto.
  * rewrite IHe1, IHe3, <- renn_up, IHe2. auto.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_ext_Forall. reflexivity.
    induction l; constructor.
    - destruct a. specialize (IHe (uprenn (pat_vars p) ρ)). inversion IHe. subst.
      rewrite H1, <- renn_up. reflexivity.
    - apply IHl. intros. specialize (IHe ρ0). inversion IHe. auto.
  * constructor; auto.
  * constructor.
  * constructor.
  * constructor; auto.
Qed.

Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

Theorem idrenaming_is_id : forall e, rename id e = e.
Proof.
  induction e using Exp_ind2 with
   (Q := fun l => Forall (fun e => rename id e = e) l)
   (W := fun l => Forall (fun '(_,e) => rename id e = e) l); intros; cbn; try rewrite idrenaming_upn; try rewrite idrenaming_up; try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try reflexivity.
  3-6: constructor; auto.
  all: rewrite map_ext_Forall with (g := id); auto; try rewrite map_id; try reflexivity.
  induction l; auto; inversion IHe; constructor; subst; auto.
  destruct a. rewrite idrenaming_upn, H1. reflexivity.
Qed.

Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.

Theorem idsubst_is_id : forall e, e.[idsubst] = e.
Proof.
  induction e using Exp_ind2 with (Q := fun l => Forall (fun e => e.[idsubst] = e) l)
                                  (W := fun l => Forall (fun '(_,e) => e.[idsubst] = e) l); intros; cbn; try rewrite idsubst_upn; try rewrite idsubst_up; try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try reflexivity.
  3-6: constructor; auto.
  all: rewrite map_ext_Forall with (g := id); auto; try rewrite map_id; try reflexivity.
  induction l; auto; inversion IHe; constructor; subst; auto.
  destruct a. rewrite idsubst_upn, H1. reflexivity.
Qed.

Lemma up_get_inl ξ x y:
  ξ x = inl y -> up_subst ξ (S x) = inl (rename (fun n => S n) y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

Lemma up_get_inr ξ x y:
  ξ x = inr y -> up_subst ξ (S x) = inr (S y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

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

Lemma subst_ren (σ : Renaming) (ξ : Substitution) e :
  e.[ren σ].[ξ] = e.[σ >>> ξ].
Proof.
  revert ξ σ. induction e using Exp_ind2 with 
    (Q := fun l => forall ξ σ, Forall (fun e => e.[ren σ].[ξ] = e.[σ >>> ξ]) l)
    (W := fun l => forall ξ σ, Forall (fun '(_,e) => e.[ren σ].[ξ] = e.[σ >>> ξ]) l); simpl; intros; auto.
  * rewrite <- renn_up, <- ren_up. rewrite IHe, upren_subst_up, uprenn_subst_upn. auto.
  * rewrite IHe. erewrite map_map, map_ext_Forall. reflexivity. auto.
  * rewrite <- ren_up, IHe1, IHe2, upren_subst_up. auto.
  * rewrite <- renn_up, <- ren_up. rewrite IHe1, upren_subst_up, uprenn_subst_upn.
    rewrite <- ren_up, IHe2, upren_subst_up. auto.
  * rewrite IHe1, IHe2. auto.
  * now rewrite IHe1, IHe3, <- renn_up, IHe2, uprenn_subst_upn.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (IHe _ _). inversion H. subst.
      rewrite <- renn_up, H2, uprenn_subst_upn. reflexivity.
    - apply IHl. intros. specialize (IHe ξ0 σ0). inversion IHe. auto.
Qed.

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

Theorem rename_up : forall e n σ ρ,
  rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e.
Proof.
  induction e using Exp_ind2 with
    (Q := fun l => forall n σ ρ, Forall (fun e => rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) l)
    (W := fun l => forall n σ ρ, Forall (fun '(_,e) => rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) l);
  intros; simpl; auto.
  * rewrite <- uprenn_comp. reflexivity.
  * rewrite <- uprenn_comp. reflexivity.
  * repeat fold_upn. rewrite IHe, uprenn_comp. auto.
  * erewrite IHe, map_map, map_ext_Forall. reflexivity. auto.
  * rewrite IHe1. do 2 fold_upn. rewrite IHe2. auto.
  * repeat fold_upn. rewrite IHe1, IHe2, uprenn_comp. auto.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2, IHe3, <- uprenn_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (IHe _ _ _). inversion H. subst.
      rewrite <- uprenn_comp, H2. reflexivity.
    - apply IHl. intros. epose proof (IHe _ _ _). inversion H. eauto.
Qed.

Theorem rename_comp :
  forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e.
Proof.
  induction e using Exp_ind2 with 
    (Q := fun l => forall σ ρ, Forall (fun e => rename σ (rename ρ e) = rename (ρ >>> σ) e) l)
    (W := fun l => forall σ ρ, Forall (fun '(_,e) => rename σ (rename ρ e) = rename (ρ >>> σ) e) l); intros; auto; cbn.
  * do 3 fold_upn. now rewrite rename_up.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite IHe1, IHe2, upren_comp.
  * do 2 fold_upn. now rewrite IHe1, IHe2, uprenn_comp, upren_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe3, rename_up.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (IHe _ _). inversion H. subst.
      rewrite <- uprenn_comp, H2. reflexivity.
    - apply IHl. intros. epose proof (IHe _ _). inversion H. eauto.
Qed.

Lemma subst_up_upren : forall σ ξ,
  up_subst ξ >> ren (upren σ) = up_subst (ξ >> ren σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  rewrite <- renaming_is_subst, <- renaming_is_subst. f_equiv.
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  rewrite rename_comp, rename_comp. f_equiv.
Qed.

Lemma subst_upn_uprenn : forall n σ ξ,
  upn n ξ >> ren (uprenn n σ) = upn n (ξ >> ren σ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.

Lemma ren_subst (ξ : Substitution) (σ : Renaming) e :
  e.[ξ].[ren σ] = e.[ξ >> ren σ].
Proof.
  revert ξ σ. induction e using Exp_ind2
    with (Q := fun l => forall ξ σ, Forall (fun e => e.[ξ].[ren σ] = e.[ξ >> ren σ]) l)
         (W := fun l => forall ξ σ, Forall (fun '(_,e) => e.[ξ].[ren σ] = e.[ξ >> ren σ]) l);
  simpl; intros; auto.
  * unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * do 3 fold_upn. now rewrite <- renn_up, <- subst_upn_uprenn, IHe.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite <- ren_up, <- subst_up_upren, IHe1, IHe2.
  * do 2 fold_upn. rewrite <- renn_up, <- subst_upn_uprenn, IHe1.
    replace (up_subst (ξ >> ren σ)) with (up_subst ξ >> ren (upren σ)) by apply subst_up_upren. (* rewrite does not work here for some reason *)
    now rewrite <- IHe2, <- ren_up, <-subst_up_upren.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, <- renn_up, <- subst_upn_uprenn, IHe2, IHe3.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (IHe _ _). inversion H. subst.
      rewrite <- renn_up, <- subst_upn_uprenn, H2. reflexivity.
    - apply IHl. intros. epose proof (IHe _ _). inversion H. eauto.
Qed.

Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (ξ x) eqn:P; auto.
  do 2 rewrite renaming_is_subst. rewrite ren_subst, subst_ren.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold ">>>", ">>", up_subst, shift. destruct (η n) eqn:P0; auto.
  rewrite renaming_is_subst. auto.
Qed.

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

Lemma subst_comp ξ η e :
  e.[ξ].[η] = e.[ξ >> η].
Proof.
  revert ξ η. induction e using Exp_ind2 with 
    (Q := fun l => forall ξ η, Forall (fun e => e.[ξ].[η] = e.[ξ >> η]) l)
    (W := fun l => forall ξ η, Forall (fun '(_,e) => e.[ξ].[η] = e.[ξ >> η]) l); simpl; intros; auto.
  * unfold ">>". break_match_goal; auto.
  * unfold ">>". break_match_goal; auto.
  * do 3 fold_upn. now rewrite IHe, upn_comp.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite IHe1, IHe2, up_comp.
  * do 3 fold_upn. now rewrite IHe1, IHe2, upn_comp, up_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2, upn_comp, IHe3.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe.
  * erewrite map_map, map_ext_Forall. reflexivity. auto.
    induction l; auto; constructor.
    - clear IHl. destruct a. epose proof (IHe _ _). inversion H. subst.
      rewrite H2, upn_comp. reflexivity.
    - apply IHl. intros. epose proof (IHe _ _). inversion H. eauto.
Qed.

Theorem rename_subst_core : forall e v,
  (rename (fun n : nat => S n) e).[v .:: idsubst] = e.
Proof.
  intros.
  rewrite renaming_is_subst, subst_comp. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id. reflexivity.
Qed.

Theorem rename_subst : forall e v,
  (rename (fun n : nat => S n) e).[v/] = e.
Proof.
  intros. apply rename_subst_core.
Qed.

Lemma scons_substcomp_core v ξ η :
  (v .:: ξ) >> η = match v with 
                   | inl exp => inl (exp.[η])
                   | inr n => η n
                   end .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.

Lemma scons_substcomp v ξ η :
  (v .: ξ) >> η = v.[η] .: (ξ >> η).
Proof.
  apply scons_substcomp_core.
Qed.

Lemma scons_substcomp_list ξ η vals :
  (list_subst vals ξ) >> η = list_subst (map (subst η) vals) (ξ >> η).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.

Lemma substcomp_scons_core v ξ η :
  up_subst ξ >> v .:: η = v .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  rewrite renaming_is_subst, subst_comp. f_equiv.
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

Theorem subst_extend_core : forall ξ v,
  (up_subst ξ) >> (v .:: idsubst) = v .:: ξ.
Proof.
  intros. unfold substcomp. extensionality x. destruct x; auto.
  cbn. break_match_goal.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. rewrite rename_subst_core. auto.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. cbn. reflexivity.
Qed.

Theorem subst_extend : forall ξ v,
  (up_subst ξ) >> (v .: idsubst) = v .: ξ.
Proof.
  intros. apply subst_extend_core.
Qed.

Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (upn n ξ) >> (list_subst vals idsubst) = list_subst vals ξ.
Proof.
  induction n; intros.
  * apply length_zero_iff_nil in H. subst. cbn. unfold substcomp. extensionality x.
    break_match_goal; try rewrite idsubst_is_id; try reflexivity.
  * simpl. apply eq_sym in H as H'. apply element_exist in H'. destruct H', H0. subst.
    simpl. rewrite substcomp_scons. rewrite IHn; auto.
Qed.

Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals (ELit 0)).
Proof.
  induction n; intros; destruct vals.
  * inversion H.
  * simpl. auto.
  * inversion H.
  * simpl in H. apply Lt.lt_S_n in H. eapply IHn in H. simpl. exact H.
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
  list_subst vals ξ n = inl (nth n vals (ELit 0)) /\ n < length vals
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
  break_match_goal; auto. rewrite idsubst_is_id. auto.
Qed.

Lemma substcomp_id_l :
  forall ξ, idsubst >> ξ = ξ.
Proof.
  unfold ">>", idsubst. intros. extensionality x. auto.
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
  now rewrite <- renaming_is_subst.
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
  rewrite subst_comp. reflexivity.
Qed.