Require Import inductionAndFunctions.

Section unfoldSimplAndReflexivity.

  Lemma twicePlusOneIsPlusTwo {x:threeElementSet}:
    plusOneModThree (plusOneModThree x) = plusTwoModThree x.
  Proof.
    unfold plusTwoModThree. unfold plusOneModThree.
    induction x.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Defined.

  Lemma thirdLostAfterRounding {x y z:threeElementSet}:
    roundToPair (triple x y z) = pair x y.
  Proof.
    unfold roundToPair. simpl. reflexivity.
  Defined.

  Example testAppend {x y z:threeElementSet}:
    append (cons x nil) (cons y (cons z nil)) =
    cons x (cons y (cons z nil)).
  Proof.
    simpl. reflexivity. Defined.

End unfoldSimplAndReflexivity.

Section rewrite.

  Lemma appendAssoc (l m n:lst):
    append (append l m) n = append l (append m n).
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
  Defined.

End rewrite.