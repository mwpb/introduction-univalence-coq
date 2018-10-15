Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Print LoadPath.
Require Import equivalencesDefinitions.
Require Import propositionsSets.

Section contractibleMaps.

Axiom funcExt:
  forall X:Type, forall B:X->Type,
  forall H0 H1:forall x:X, B x,
  (forall x:X, Id (H0 x) (H1 x)) -> Id H0 H1.

Definition isContractibleImpliesIsSet (X:Type):
IsContractible X -> IsSet X.
Proof.
intro. induction X0. apply isSet. intros. 
assert (Id p (comp (reverse (H x0)) (H x1))).
- induction p. induction (H x). simpl. apply refl.
- intros. assert (Id q (comp (reverse (H x0)) (H x1))).
  -- induction q. induction (H x). simpl. apply refl.
  -- induction X0. induction X1. apply refl.
Defined.

Definition isContractibleIsProp (X:Type):
IsProp(IsContractible X).
Proof.
apply isProp. intros K L.
apply isContractibleImpliesIsSet in K as M.
induction L, K, M. assert (Id c c0).
- induction (H0 c). apply refl.
- induction X0. assert (forall x0:X, Id (H x0) (H0 x0)).
-- intro. induction (H1 x x0 (H0 x0) (H x0)). apply refl.
-- apply (funcExt X (Id x) H H0) in X0. induction X0.
    apply refl.
Defined.

Definition dependentProps {X:Type} (B:X->Type):
(forall x:X, IsProp(B x)) -> IsProp(forall x:X,B x).
Proof.
intro H. apply isProp. intros L M. 
assert (forall x:X, Id (L x) (M x)).
- intro. induction (H x). induction (H0 (L x) (M x)).
  apply refl.
- apply funcExt. intro. apply (X0 x).
Defined.

Definition isContractibleMapIsProp {X Y:Type} (f:X->Y):
  IsProp(IsContractibleMap f).
Proof.
apply isProp. intros. induction x0, x1.
assert (forall y:Y, IsProp(IsContractible (Fibre f y))).
- intro. apply isContractibleIsProp.
- assert (Id H0 H).
-- apply funcExt. intro. induction (X0 x).
    induction (H1 (H x) (H0 x)). apply refl.
-- induction X1. apply refl.
Defined.

End contractibleMaps.

Section allImplyQinv.

Definition halfAdjointImpliesQinv {X Y:Type} (f:X->Y):
HalfAdjointEquiv f -> Qinv f.
Proof.
intro p. induction p. apply (qinv f g).
- apply n.
- apply e.
Defined.

Definition biinvImpliesQinv {X Y:Type} (f:X->Y):
  Biinv f -> Qinv f.
Proof.
  intro. induction X0. apply (qinv f g n).
  intros.
  specialize e with y as e0. specialize n with (h y) as n0.
  specialize e with y as e1.
  apply appl with g in e0. apply appl with f in e0.
  apply appl with f in n0. induction e1. apply n0.
Defined.

Definition invOfContractibleMap {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  Y->X.
Proof.
intro y. induction H. induction (H y).
induction c. apply x.
Defined.

Definition invIsSection {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  forall y:Y, Id (f(invOfContractibleMap f H y)) y.
Proof.
intro. induction H. simpl. induction (H y).
simpl. induction c. apply H1.
Defined.

Definition fibreInclusion {X Y:Type} (f:X->Y) (y:Y):
Fibre f y -> X.
Proof.
intro. induction X0. apply x.
Defined.

Definition invIsRetraction {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  forall x:X, Id (invOfContractibleMap f H (f x)) x.
Proof.
intro. unfold invOfContractibleMap. unfold IsContractible_rect.
simpl. unfold IsContractibleMap_rect. simpl. induction H. simpl.
induction (H (f x)). simpl. induction c. simpl.
specialize H0 with (fibre f (f x) x (refl (f x))).
apply (appl (fibreInclusion f (f x))) in H0.
simpl in H0. apply H0.
Defined.

Definition isContractibleMapImpliesQinv {X Y:Type} (f:X->Y):
IsContractibleMap f -> Qinv f.
Proof.
intro. induction X0.
apply (qinv f (invOfContractibleMap f (isContractibleMap f H))).
- apply invIsRetraction.
- apply invIsSection.
Defined.

End allImplyQinv.

Section halfAdjointEquivContr.

Definition idInFibres {X Y:Type} 
  (f:X->Y) (y:Y) (x0 x1:X) (H0:Id (f x0) y) (H1:Id (f x1) y)
  (gamma:Id x0 x1) (K: Id (comp (appl f gamma) H1) H0):
  Id (fibre f y x0 H0) (fibre f y x1 H1).
Proof.
induction gamma. simpl in K. induction K. apply refl.
Defined.

Definition reverseInvolution {X:Type} {x0 x1:X}
  (f:Id x0 x1):
  Id (reverse (reverse f)) f.
Proof.
induction f. simpl. apply refl.
Defined.

Definition functoriality {X Y:Type} {x0 x1 x2:X} {f:X->Y}
  {p:Id x0 x1} {q:Id x1 x2}:
  Id (comp (appl f p) (appl f q)) (appl f (comp p q)).
Proof.
induction p. induction q. simpl. apply refl.
Defined.

Definition idInFibresAlt {X Y:Type} 
  (f:X->Y) (y:Y) (x0 x1:X) (H0:Id (f x0) y) (H1:Id (f x1) y)
  (gamma:Id x0 x1) (K: Id (appl f gamma) (comp H0 (reverse H1))):
  Id (fibre f y x0 H0) (fibre f y x1 H1).
Proof.
assert (Id (comp (appl f gamma) H1) H0).
- induction gamma. simpl in K. assert (Id H1 H0).
-- induction H0. simpl in K. apply reverse.
    apply (appl reverse) in K. simpl in K.
    assert (Id (reverse (reverse H1)) H1).
--- apply reverseInvolution. 
--- induction X0. apply K.
-- induction X0. simpl. apply refl.
- apply (idInFibres
          f
          y
          x0
          x1
          H0
          H1
          gamma).
apply X0.
Defined.

Definition halfAdjointEquivImpliesContractible {X Y:Type}
  (f:X->Y):
  HalfAdjointEquiv f -> IsContractibleMap f.
Proof.
intro. induction X0. apply isContractibleMap.
intro. 
apply (isContractible
        (Fibre f y)
        (fibre f y (g y) (e y))).
intro p. induction p.
apply (idInFibresAlt
        f
        y
        (g y)
        x
        (e y)
        H
        (comp (reverse (appl g H)) (n x))).
assert (Id  (appl f (comp (reverse (appl g H)) (n x)))
            (comp (appl f (reverse (appl g H))) (appl f (n x)))).
-- apply reverse. apply functoriality.
-- assert (Id (appl f (comp (reverse (appl g H)) (n x)))
            (comp (appl f (reverse (appl g H))) (e(f x)))).
--- induction (t x). apply X0.
--- apply (comp X1). clear X0. clear X1. induction H.
    simpl. induction (e x0). simpl. apply refl.
Defined.

End halfAdjointEquivContr.









