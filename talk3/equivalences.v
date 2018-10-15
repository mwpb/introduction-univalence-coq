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
(* your proof here *)
Defined.

Definition isContractibleMapIsProp {X Y:Type} (f:X->Y):
  IsProp(IsContractibleMap f).
Proof.
(* your proof here - one way is to assert a 
  statement beginning forall y:Y, ___ *)
Defined.

End contractibleMaps.

Section allImplyQinv.

Definition halfAdjointImpliesQinv {X Y:Type} (f:X->Y):
HalfAdjointEquiv f -> Qinv f.
Proof.
(* your proof here *)
Defined.

Definition biinvImpliesQinv {X Y:Type} (f:X->Y):
  Biinv f -> Qinv f.
Proof.
(* your proof here *)
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
(* your proof here *)
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
(* your proof here *)
Defined.

End allImplyQinv.

Section halfAdjointEquivContr.

Definition idInFibres {X Y:Type} 
  (f:X->Y) (y:Y) (x0 x1:X) (H0:Id (f x0) y) (H1:Id (f x1) y)
  (gamma:Id x0 x1) (K: Id (comp (appl f gamma) H1) H0):
  Id (fibre f y x0 H0) (fibre f y x1 H1).
Proof.
(* your proof here *)
Defined.

Definition reverseInvolution {X:Type} {x0 x1:X}
  (f:Id x0 x1):
  Id (reverse (reverse f)) f.
Proof.
(* your proof here *)
Defined.

Definition functoriality {X Y:Type} {x0 x1 x2:X} {f:X->Y}
  {p:Id x0 x1} {q:Id x1 x2}:
  Id (comp (appl f p) (appl f q)) (appl f (comp p q)).
Proof.
(* your proof here *)
Defined.

Definition idInFibresAlt {X Y:Type} 
  (f:X->Y) (y:Y) (x0 x1:X) (H0:Id (f x0) y) (H1:Id (f x1) y)
  (gamma:Id x0 x1) (K: Id (appl f gamma) (comp H0 (reverse H1))):
  Id (fibre f y x0 H0) (fibre f y x1 H1).
Proof.
(* your proof here - this is a long proof *)
Defined.

Definition halfAdjointEquivImpliesContractible {X Y:Type}
  (f:X->Y):
  HalfAdjointEquiv f -> IsContractibleMap f.
Proof.
(* your proof here - this is a long proof *)
Defined.

End halfAdjointEquivContr.









