Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Require Import univalence.
Require Import equivalences.
Require Import equivalencesDefinitions.
Require Import propositionsSets.

Section prodStrictlyAssoc.
Search prod.

Definition associator (X Y Z:Type):
  (prod (prod X Y) Z) -> (prod X (prod Y Z)).
Proof.
  intro. induction X0. induction a.
  apply (a,(b0,b)).
Defined.

Definition associatorInverse (X Y Z:Type):
  (prod X (prod Y Z)) -> (prod (prod X Y) Z).
Proof.
  intro. induction X0. induction b.
  apply (a, a0, b).
Defined.

Definition assocInv {X Y Z:Type} (v:(prod X (prod Y Z))):
  Id (associator X Y Z (associatorInverse X Y Z v)) v.
Proof.
induction v. induction b. simpl. apply refl.
Defined.

Definition assocInv2 {X Y Z:Type} (v:prod (prod X Y) Z):
  Id (associatorInverse X Y Z (associator X Y Z v)) v.
Proof.
induction v. induction a. simpl. apply refl.
Defined.

Definition associatorIsEquiv {X Y Z:Type}:
  IsContractibleMap (associator X Y Z).
Proof.
apply halfAdjointEquivImpliesContractible.
apply (halfAdjointEquiv
        (associator X Y Z)
        (associatorInverse X Y Z)
        assocInv2
        assocInv
        ).
intro x. induction x. induction a. simpl.
apply refl.
Defined.

Lemma productStrictlyAssoc {X Y Z:Type}:
  Id (prod (prod X Y) Z) (prod X (prod Y Z)).
Proof.
  apply univalence.
  apply (isEquiv (prod (prod X Y) Z) (prod X (prod Y Z)) (associator X Y Z)).
  apply associatorIsEquiv.
Defined.

End prodStrictlyAssoc.