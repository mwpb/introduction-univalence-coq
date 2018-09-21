Section induction.

  Inductive threeElementSet:=
  |zero
  |one
  |two.

  Inductive pairOrTriple:=
  |pair (x y:threeElementSet)
  |triple (x y z:threeElementSet).

  Inductive lst:=
  |nil
  |cons (x:threeElementSet) (l:lst).

End induction.

Section functions.

  Definition plusOneModThree (X:threeElementSet):
    threeElementSet.
  Proof.
    induction X.
    - apply one.
    - apply two.
    - apply zero.
  Defined.

  Definition constantAtZero (X:threeElementSet):
    threeElementSet.
  Proof.
    apply zero.
  Defined.

  (* Exercise *)
  Definition plusTwoModThree (X:threeElementSet):
    threeElementSet.
  Proof.
    induction X.
    - apply three.
    - apply one.
    - apply two.
  Defined.

  Definition roundToPair (p:pairOrTriple):
    pairOrTriple.
  Proof.
    induction p.
    - apply (pair x y).
    - apply (pair x y).
  Defined.

  Fixpoint append (l m:lst):
    lst.
  Proof.
    destruct l.
    - apply m.
    - apply (cons x (append l m)).
  Defined.

End functions.