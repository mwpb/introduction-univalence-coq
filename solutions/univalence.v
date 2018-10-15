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
  intro. induction X0.
  - apply (isEquiv x x (id x)).
    apply isContractibleMap. intro x0.
    apply (isContractible (Fibre (id x) x0) (fibre (id x) x0 x0 (refl x0))).
    intro p. induction p. unfold id in H.
    induction H. apply refl.
Defined.

Axiom univalence:
  forall X Y:Type, IsContractibleMap(idToEquiv X Y).

End univalence.