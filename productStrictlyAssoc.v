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
    (* define the function ((x, y), z) |-> (x, (y, z)) *)
  Defined.

  Definition associatorInverse (X Y Z:Type):
    (prod X (prod Y Z)) -> (prod (prod X Y) Z).
  Proof.
    (* define the function (x, (y, z)) |-> ((x, y), z)*)
  Defined.

  Definition associatorIsEquiv {X Y Z:Type}:
    IsEquiv (associator X Y Z).
  Proof.
    (* your proof here *)
  Defined.
  
  Lemma productStrictlyAssoc {X Y Z:Type}:
    Id (prod (prod X Y) Z) (prod X (prod Y Z)).
  Proof.
    (* your proof here *)
  Defined.

End prodStrictlyAssoc.