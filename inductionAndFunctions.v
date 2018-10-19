Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Section inductionExamples.

  Inductive ThreeElementSet:=
  |zero
  |one
  |two.

  Inductive PairOrTriple:=
  |pair (x y:ThreeElementSet)
  |triple (x y z:ThreeElementSet).

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
  (* define four element set *).
  
  Inductive Nat:=
  (* define natural number induction *).

End inductionExercises.

Section functionExercises.

  Definition constantAtZero4 (x:FourElementSet):
    FourElementSet.
  Proof.
    (* define the function x|->0*)
  Defined.

  Definition doubleModThree (x:ThreeElementSet):
    ThreeElementSet.
  Proof.
    (* define the function x|->2x (mod 3)*)
  Defined.

  Definition fourModThree (x:FourElementSet):
    ThreeElementSet.
  Proof.
    (* define the function x|->x( mod 3) 
       that lands in ThreeElementSet *)
  Defined.

  Fixpoint length (l:Lst):
    Nat.
  Proof.
    (* return the length of l *)
  Defined.

End functionExercises.













