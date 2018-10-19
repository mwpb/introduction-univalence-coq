Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Require Import Coq.Program.Tactics.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Set Printing Universes.
Require Import propositionsSets.

Section wrongUnivalence.

Inductive IsEquivMap {X Y:Type} (f:X->Y):=
|isEquivMap (g:Y->X)
     (H1:forall x:X, Id (g(f(x))) x)
     (H2:forall y:Y, Id (f(g(y))) y).

Inductive IsEquiv (X Y:Type):=
|isEquiv (f:X->Y) (H:IsEquivMap f).

Definition idToEquiv (X Y:Type):
  Id X Y -> IsEquiv X Y.
Proof.
intro. induction X0.
- apply (isEquiv x x (id x)).
  apply (isEquivMap (id x) (id x)).
  -- intros. apply refl.
  -- intros. apply refl.
Defined.

Axiom univalence:
  forall X Y:Type, IsEquivMap(idToEquiv X Y).

Definition reverseIdToEquiv {X Y:Type}:
  IsEquiv X Y -> Id X Y.
Proof.
assert (forall X Y:Type, IsEquivMap(idToEquiv X Y)).
- apply univalence.
- specialize X0 with X Y. intro. induction X0. 
  apply g. apply X1.
Defined.

Inductive Two:Type:=
|first
|second.

Inductive CE :=
|inCE (X:Type) (H:notT (notT (Id (Two:Type) X))).

Definition reductio:
  False.
Proof.
assert (IsProp(forall x:CE, Id x x)).
-



















End wrongUnivalence.