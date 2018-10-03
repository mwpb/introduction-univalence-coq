Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Require Export univalenceSolutions.

Section equivalencesDefinitions.

Inductive Qinv {X Y:Type} (f:X->Y):=
|qinv 
  (g:Y->X)
  (n:forall x:X, Id (g(f(x))) x)
  (e:forall y:Y, Id (f(g(y))) y).
  
Definition appl {X Y:Type} {x0 x1:X} (f:X->Y) (H:Id x0 x1):
Id (f(x0)) (f(x1)).
Proof.
induction H. apply refl.
Defined.

Definition happl {X:Type} {x0 x1:X} (f:X->Type) (H:Id x0 x1):
Id (f(x0)) (f(x1)).
Proof.
induction H. apply refl.
Defined.

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

Inductive IsContractible (X:Type):=
|isContractible 
  (x:X)
  (H:forall x0 x1:X, Id x0 x1).
  
Inductive Fibre {X Y:Type} (f:X->Y) (y:Y):=
|fibre
  (x:X)
  (H:Id (f(x)) y).

Inductive IsContractibleMap {X Y:Type} (f:X->Y):=
|isContractibleMap
  (H:forall y:Y, forall x0 x1:X, Id (f(x0)) (f(x1)) -> Id x0 x1)
  (K:forall y:Y, Fibre f y).
  
End equivalencesDefinitions.