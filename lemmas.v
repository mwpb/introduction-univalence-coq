Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Require Import Coq.Program.Tactics.
Require Import inductionAndFunctions.

Section lemmasExamples.

  Definition twicePlusOneIsPlusTwo:
    forall x:ThreeElementSet,
      plusOneModThree (plusOneModThree x) = plusTwoModThree x.
  Proof.
  intros. induction x.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  Defined.

  Definition thirdLostAfterRounding:
    forall x y z:ThreeElementSet,
      roundToPair (triple x y z) = pair x y.
  Proof.
  intros. simpl. reflexivity.
  Defined.

  Definition testAppend {x y z:ThreeElementSet} {l:Lst}:
    append (cons x nil) (cons y (cons z l)) =
    cons x (cons y (cons z l)).
  Proof.
  simpl. reflexivity. 
  Defined.

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
      fourModThree (constantAtZero4 x) =
      constantAtZero (fourModThree x).
  Proof.
  (* your proof here *)
  Defined.

  Definition doubleModThreeIdempotent:
    forall x:ThreeElementSet,
      doubleModThree (doubleModThree x) = x.
  Proof.
  (* your proof here *)
  Defined.

  Definition lengthDoubleCons:
    forall x y:ThreeElementSet,
    forall l:Lst,
      length (cons y (cons x l)) = succ (succ (length l)).
  Proof.
  (* your proof here *)
  Defined.
  
  Definition appendHigherAssoc (l1 l2 l3 l4:Lst):
  append l1 (append l2 (append l3 l4)) = 
  append (append(append l1 l2) l3) l4.
  Proof.
  (* your proof here *)
  Defined.
  
  Definition lengthLemma (l1 l2:Lst) (x:ThreeElementSet):
  length (append l1 (append (cons x nil) l2)) =
  succ ( length (append l1 l2)).
  Proof.
  (* your proof here *)
  Defined.

End lemmasExercises.