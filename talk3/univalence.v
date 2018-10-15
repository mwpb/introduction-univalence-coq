Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Set Printing Universes.
Require Import propositionsSets.
Require Import equivalencesDefinitions.

Section univalence.

Inductive IsEquiv (X Y:Type):=
|isEquiv (f:X->Y) (H:IsContractibleMap f).

Definition idToEquiv (X Y:Type):
  Id X Y -> IsEquiv X Y.
Proof.
(* your proof here *)
Defined.

Axiom univalence:
  forall X Y:Type, IsContractibleMap(idToEquiv X Y).

End univalence.