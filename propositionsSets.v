Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Require Import univalenceSolutions.

Section propositionsSets.

  Inductive IsSingleton (X:Type) :=
  |isSingleton (c:X) (H:forall x:X, Id c x).

  Inductive IsProp (X:Type) :=
  |isProp (H:forall x y:X, Id x y).

  Inductive IsSet (X:Type) :=
  |isSet (H:forall x0 x1:X,
             IsProp (Id x0 x1)).

  Definition isSetAlt1 (X:Type):
    (IsSet X ->
     (forall x0 x1:X,
     forall f g: Id x0 x1,
       Id f g)).
  Proof.
    intros. apply X0.
  Defined.

  Definition isSetAlt2 (X:Type):
    ((forall x0 x1:X,
     forall f g: Id x0 x1,
       Id f g) ->
    IsSet X).
  Proof.
    intros. apply isSet. intros. apply isProp. intros.
    specialize X0 with (x0:=x0) (x1:=x1) (f:=x) (g:=y).
    apply X0.
  Defined.

  Axiom funcExt:
    forall X Y:Type,
    forall g f:X->Y,
      (forall x:X, Id (f(x)) (g(x))) -> Id f g.

  Definition IsEquivIsProp {X Y:Type} (f:X->Y):
    IsProp (IsEquiv f).
  Proof.
    apply isProp. induction x. intro. apply funcExt.

https://homotopytypetheory.org/2012/06/01/hequiv-equiv-take-3/
    
    