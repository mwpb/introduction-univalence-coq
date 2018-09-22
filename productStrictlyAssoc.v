Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Require Import univalenceSolutions.

Section prodStrictlyAssoc.
Search prod.

  Definition associator (X Y Z:Type):
    (prod (prod X Y) Z) -> (prod X (prod Y Z)).
  Proof.
    intro. induction X0. induction a.
    apply (a,(b0,b)).
  Defined.

  Definition associatorIsEq {X Y Z:Type}:
    IsEq (associator X Y Z).
  Proof.
    (* your proof here: requires inversion tactic *)
  Defined.
  
  Lemma productStrictlyAssoc {X Y Z:Type}:
    Id (prod (prod X Y) Z) (prod X (prod Y Z)).
  Proof.
    (* your proof here *)
  Defined.

End prodStrictlyAssoc.