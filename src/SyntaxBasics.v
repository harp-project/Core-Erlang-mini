From CoreErlang Require Export Basics.

(** Process identifiers are regarded as nats *)
Definition PID : Set := nat.

(** Currently, we include atoms and integers as literals. We note that 
    atoms are also used for built-in function names.
*)
Inductive Lit : Set :=
| Atom (s : string)
| Int (z : Z).

(** Coercions to be able to write down literals in a simpler way. *)
Coercion Atom : string >-> Lit.
Coercion Int  : Z >-> Lit.

(** Patterns are the following contructs. Patterns variables in Core
    Erlang are unique, they can appear at most once in any Pattern.
    Because of this, in the nameless representation, no indices
    are needed for pattern variables.

    For technical reasons, PIDs are included as patterns, but they could
    be omitted by implementing the function erlang:is_pid/1.

    We note, that this resriction is not applicable for Erlang, though.
*)
Inductive Pat : Set :=
| PLit (l : Lit)
| PPid (p : PID)
| PVar (** will be assigned in increasing order *)
| PNil
| PCons (p1 p2 : Pat).



Definition lit_eqb (l1 l2 : Lit) : bool :=
match l1, l2 with
 | Atom s, Atom s2 => String.eqb s s2
 | Int z , Int z2  => Z.eqb z z2
 | _     , _       => false
end.

Lemma lit_eqb_eq : forall l1 l2, lit_eqb l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; split; intros; subst; auto; simpl in H; try congruence.
  * apply eqb_eq in H. now inversion H.
  * inversion H. subst. simpl. now rewrite eqb_refl.
  * apply Z.eqb_eq in H. now inversion H.
  * inversion H. subst. simpl. now rewrite Z.eqb_refl.
Qed.

Lemma lit_eqb_refl : forall l, lit_eqb l l = true.
Proof.
  intro. rewrite lit_eqb_eq. reflexivity.
Qed.
