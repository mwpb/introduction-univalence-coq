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

(*

Definition naturality {X Y:Type} {x0 x1:X} 
  (f g:X->Y) (H:forall x:X, Id (f(x)) (g(x)))
  (p:Id x0 x1):
  forall x:X, Id (comp (H x0) (appl g p)) (comp (appl f p) (H x1)).
Proof.
intro. simpl. induction p. simpl.
induction (H x0). simpl. apply refl.
Defined. 

Definition happl {X:Type} {x0 x1:X} (f:X->Type) (H:Id x0 x1):
Id (f(x0)) (f(x1)).
Proof.
induction H. apply refl.
Defined.


*)