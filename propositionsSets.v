Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Section propositionsSets.

Inductive Id {X:Type}:X->X->Type:=
|refl (x:X): Id x x.

Definition id (X:Type) (x:X):
  X.
Proof.
  apply x.
Defined.

Definition comp {X:Type} {x0 x1 x2:X}
  (f:Id x0 x1) (g:Id x1 x2):
  Id x0 x2.
Proof.
induction f. apply g.
Defined.


Definition reverse {X:Type} {x0 x1:X}
(f:Id x0 x1):
Id x1 x0.
Proof.
induction f. apply refl.
Defined.

Definition appl {X Y:Type} {x0 x1:X} (f:X->Y) (H:Id x0 x1):
Id (f(x0)) (f(x1)).
Proof.
induction H. apply refl.
Defined.

Inductive IsProp (X:Type):=
|isProp (H:forall x0 x1:X, Id x0 x1).

Inductive IsSet (X:Type):=
|isSet (H:forall x0 x1:X, forall p q:Id x0 x1, Id p q).

Inductive IsContractible (X:Type):=
|isContractible 
  (c:X)
  (H:forall x:X, Id c x).

End propositionsSets.