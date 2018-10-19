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

(*  the proof of the following Lemma is at 
    the end of equivalences.v. *)
Definition halfAdjointEquivImpliesContractible {X Y:Type}
  (f:X->Y):
  HalfAdjointEquiv f -> IsContractibleMap f.
Proof.
Admitted.

Definition associator (X Y Z:Type):
  (prod (prod X Y) Z) -> (prod X (prod Y Z)).
Proof.
  intro. induction X0. induction a.
  apply (a,(b0,b)).
Defined.

Definition associatorInverse (X Y Z:Type):
  (prod X (prod Y Z)) -> (prod (prod X Y) Z).
Proof.
(* define the inverse to the associator here *)
Defined.

Definition assocIsInv {X Y Z:Type} (v:(prod X (prod Y Z))):
  Id (associator X Y Z (associatorInverse X Y Z v)) v.
Proof.
(* your proof here *)
Defined.

Definition assocIsInv2 {X Y Z:Type} (v:prod (prod X Y) Z):
  Id (associatorInverse X Y Z (associator X Y Z v)) v.
Proof.
(* your proof here *)
Defined.



Definition associatorIsEquiv {X Y Z:Type}:
  IsContractibleMap (associator X Y Z).
Proof.
(* your proof here - use the fact that haequiv are contractible maps *)
Defined.

Lemma productStrictlyAssoc {X Y Z:Type}:
  Id (prod (prod X Y) Z) (prod X (prod Y Z)).
Proof.
(* your proof here *)
Defined.

End prodStrictlyAssoc.