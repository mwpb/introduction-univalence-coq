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

  Definition associatorInverse (X Y Z:Type):
    (prod X (prod Y Z)) -> (prod (prod X Y) Z).
  Proof.
    intro. induction X0. induction b.
    apply (a, a0, b).
  Defined.

  Definition associatorIsEquiv {X Y Z:Type}:
    IsEquiv (associator X Y Z).
  Proof.
    apply (isEquiv (associator X Y Z) (associatorInverse X Y Z) (associatorInverse X Y Z)).
    - intros. induction x. induction a. apply refl.
    - intros. induction y. induction b. simpl. apply refl.
  Defined.
  
  Lemma productStrictlyAssoc {X Y Z:Type}:
    Id (prod (prod X Y) Z) (prod X (prod Y Z)).
  Proof.
    apply univalence.
    apply (eq (prod (prod X Y) Z) (prod X (prod Y Z)) (associator X Y Z)).
    apply associatorIsEquiv.
  Defined.

End prodStrictlyAssoc.