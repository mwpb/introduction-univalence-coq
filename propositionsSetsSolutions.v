Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Require Import univalenceSolutions.

Section propositionsSets.

  Axiom funcExt:
    forall A:Type, forall (B:A->Type),
    forall (g f:forall x:A, B x),
    (forall x:A, Id (f x) (g x)) -> Id f g.

  Inductive IsProp (X:Type) :=
  |isProp (H:forall x y:X, Id x y).
  
  Definition dependentProp {X:Type} {B:X->Type}:
  (forall x:X, IsProp (B x)) -> IsProp (forall x:X, B x).
  Proof.
  intro. apply isProp. intros p q. apply funcExt. intro.
  specialize X0 with x. induction X0. induction (H (p x) (q x)). apply refl.
  Defined.
  
  Inductive IsContractible (X:Type) :=
  |isContractible (x:X) (H:IsProp X).

  Inductive IsSet (X:Type) :=
  |isSet (H:forall x0 x1:X,
             IsProp (Id x0 x1)).

  Inductive Fibre {X Y:Type} (f:X->Y) (y:Y):=
  |fibre (x:X) (H: Id (f(x)) y).
  
  Inductive IsContractibleMap {X Y:Type} (f:X->Y):=
  |isContractibleMap (H:forall y:Y, IsContractible(Fibre f y)).

End propositionsSets.