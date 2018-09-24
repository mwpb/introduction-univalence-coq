Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Section inductionExamples.

  Inductive ThreeElementSet:=
  |zero
  |one
  |two.
  
  Compute zero.

  Inductive PairOrTriple:=
  |pair (x y:ThreeElementSet)
  |triple (x y z:ThreeElementSet).
  
  Compute pair.

  Inductive Lst:=
  |nil
  |cons (x:ThreeElementSet) (l:Lst).

End inductionExamples.

Section functionExamples.

  Definition plusOneModThree (X:ThreeElementSet):
    ThreeElementSet.
  Proof.
    induction X.
    - apply one.
    - apply two.
    - apply zero.
  Defined.

  Definition constantAtZero (X:ThreeElementSet):
    ThreeElementSet.
  Proof.
    apply zero.
  Defined.

  Definition plusTwoModThree (X:ThreeElementSet):
    ThreeElementSet.
  Proof.
    induction X.
    - apply two.
    - apply zero.
    - apply one.
  Defined.

  Definition roundToPair (p:PairOrTriple):
    PairOrTriple.
  Proof.
    induction p.
    - apply (pair x y).
    - apply (pair x y).
  Defined.

  Fixpoint append (l m:Lst):
    Lst.
  Proof.
    destruct l.
    - apply m.
    - apply (cons x (append l m)).
  Defined.

End functionExamples.

Section inductionExercises.

  Inductive FourElementSet:=
  |zero4
  |one4
  |two4
  |three4.

  Inductive Nat:=
  |base
  |succ (n:Nat).

End inductionExercises.

Section functionExercises.

  Definition constantAtZero4 (x:FourElementSet):
    FourElementSet.
  Proof.
    (* x |-> zero4 *)
  Defined.

  Definition doubleModThree (x:ThreeElementSet):
    ThreeElementSet.
  Proof.
    (* x |-> 2x mod 3 *)
  Defined.

  Definition fourModThree (x:FourElementSet):
    ThreeElementSet.
  Proof.
    (*x|->x mod 3*)
  Defined.

  Fixpoint length (l:Lst):
    Nat.
  Proof.
    (* returns the length of l *)
  Defined.

End functionExercises.













