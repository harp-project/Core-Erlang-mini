Require Import LogRel.
Import ListNotations.

Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  exists v1 v2, (* Vrel v1 v2 /\  <- here n-independent equivalence needed *)
  (exists clock, eval clock e1 = Res v1) <-> (exists clock, eval clock e2 = Res v2). 