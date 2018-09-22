Require Import univalence.

Section prodStrictlyAssoc.

  Definition associator (X Y Z:Type):
    (prod (prod X Y) Z) -> (prod X (prod Y Z)).
  Proof.
    intro. induction X0. induction a.
    apply (a,(b0,b)).
  Defined.

  Definition associatorIsEq {X Y Z:Type}:
    IsEq (associator X Y Z).
  Proof.
    apply isEq.
    - intros. induction x0,x1. induction a,p.
      simpl in X0. inversion X0. apply refl.
    - intros. induction y. induction b. apply (preim (associator X Y Z) (a, (a0,b)) ((a, a0),b)).
      simpl. apply refl.
  Defined.
  
  Lemma productStrictlyAssoc {X Y Z:Type}:
    Id (prod (prod X Y) Z) (prod X (prod Y Z)).
  Proof.
    apply univalence.
    apply (eq (prod (prod X Y) Z) (prod X (prod Y Z)) (associator X Y Z)).
    apply associatorIsEq.
  Defined.

End prodStrictlyAssoc.b