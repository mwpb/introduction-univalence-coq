Require Import inductionAndFunctions.

Section lemmasExamples.

  Definition twicePlusOneIsPlusTwo:
    forall x:ThreeElementSet,
      plusOneModThree (plusOneModThree x) = plusTwoModThree x.
  Proof.
    unfold plusTwoModThree. unfold plusOneModThree.
    induction x.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Defined.

  Definition thirdLostAfterRounding:
    forall x y z:X,
      roundToPair (triple x y z) = pair x y.
  Proof.
    unfold roundToPair. simpl. reflexivity.
  Defined.

  Definition testAppend {x y z:ThreeElementSet} {l:Lst}:
    append (cons x nil) (cons y (cons z l)) =
    cons x (cons y (cons z l)).
  Proof.
    simpl. reflexivity. Defined.

  Definition appendAssoc (l m n:Lst):
    append (append l m) n = append l (append m n).
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
  Defined.

End lemmasExamples.

Section lemmasExercises.

  Definition constantModThree:
    forall x:FourElementSet,
      fourModThree (constantAtZero x) =
      constantAtZero (fourModThree x).
  Proof.
    (* proof here *)
  Defined.

  Definition doubleModThreeIdempotent:
    forall x:ThreeElementSet,
      doubleModThree (doubleModThree x) = x.
  Proof.
    (* proof here *)
  Defined.

  Definition lengthDoubleCons:
    forall x y:ThreeElementSet,
    forall l:Lst,
      length (cons y (cons x l)).
  Proof.
    (* proof here *)
  Defined.

Section lemmasExercises.