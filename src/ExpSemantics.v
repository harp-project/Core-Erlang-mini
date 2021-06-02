Require Export ExpSyntax.
From Coq Require Export micromega.Lia.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Import ListNotations.

Section functional_semantics.

Fixpoint eval_list (f : Exp -> option Exp) (l : list Exp) : option (list Exp) :=
match l with
| [] => Some []
| x::xs => match f x with
           | Some v => match eval_list f xs with
                       | Some vs => Some (v::vs)
                       | None => None
                       end
           | None => None
           end
end.

Fixpoint eval (clock : nat) (e : Exp) : option Exp :=
match clock with
| 0 => None
| S n => match e with
         | ELit l => Some (ELit l)
         | EVar v => None
         | EFunId f => None
         | EFun vl e => Some (EFun vl e)
         | ERecFun f vl e => Some (ERecFun f vl e)
         | EApp exp l => match eval n exp with
                         (** In Core Erlang this check only happens later *)
                         | Some (EFun vl e) =>
                            (* This would be better with Monads *)
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Some vals => eval n (varsubst_list vl vals e)
                               | None => None
                               end
                         | Some (ERecFun f vl e) =>
                            let vres := eval_list (eval n) l in
                               match vres with
                               | Some vals => eval n (funsubst f (ERecFun f vl e) (varsubst_list vl vals e))
                               | None => None
                               end
                         | _ => None
                         end
         | ELet v e1 e2 => match eval n e1 with
                           | Some val => eval n (varsubst v val e2)
                           | _      => None
                           end
         | ELetRec f vl b e => eval n (funsubst f (ERecFun f vl b) e)
         | EPlus e1 e2 => 
            match eval n e1, eval n e2 with
            | Some (ELit n), Some (ELit m) => Some (ELit (n + m))
            | _, _ => None
            end
         | EIf e1 e2 e3 =>
            match eval n e1 with
            | Some (ELit 0) => eval n e2
            | Some _        => eval n e3
            | None          => None
            end
        end
end.

(** Tests: *)

Goal eval 10 (inc 2) = Some (ELit 3). Proof. auto. Qed.
Goal eval 10 (simplefun 10) = Some (ELit 10). Proof. simpl. auto. Qed.
Goal eval 10 (sum 2) = Some (ELit 3). Proof. simpl. auto. Qed.
Goal eval 100 (sum 10) = Some (ELit 55). Proof. simpl. auto. Qed.
Goal eval 100 (simplefun2 10 10) = Some (ELit 20). Proof. simpl. auto. Qed.

End functional_semantics.
