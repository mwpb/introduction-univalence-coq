Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Require Import propositionsSets.

Section equivalencesDefinitions.

Inductive Qinv {X Y:Type} (f:X->Y):=
|qinv 
  (g:Y->X)
  (n:forall x:X, Id (g(f(x))) x)
  (e:forall y:Y, Id (f(g(y))) y).

Inductive HalfAdjointEquiv {X Y:Type} (f:X->Y):=
|halfAdjointEquiv 
  (g:Y->X)
  (n:forall x:X, Id (g(f(x))) x)
  (e:forall y:Y, Id (f(g(y))) y)
  (t:forall x:X, Id (appl f (n x)) (e (f x))).

Inductive Biinv {X Y:Type} (f:X->Y):=
|biinv  (g h:Y->X)
        (n:forall x:X, Id (g(f(x))) x)
        (e:forall y:Y, Id (f(h(y))) y).
  
Inductive Fibre {X Y:Type} (f:X->Y) (y:Y):=
|fibre
  (x:X)
  (H:Id (f(x)) y).

Inductive IsContractibleMap {X Y:Type} (f:X->Y):=
|isContractibleMap
  (H:forall y:Y, IsContractible(Fibre f y)).

End equivalencesDefinitions.