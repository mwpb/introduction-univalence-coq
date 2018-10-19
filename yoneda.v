Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Set Printing Universes.
Require Import univalenceSolutions.
Require Import equivalencesDefinitions.

Section yoneda.
    
  Definition pre (X:Type):= X->Type.
  
  Definition arr {X:Type} {x y:X}
             (A:pre X) (f:Id x y):
    (A x) -> (A y).
  Proof.
    induction f. apply (fun x => x). Defined.
    
  Definition natural {X:Type} (A B:pre X):Type:=
    forall x0:X, (A x0) -> (B x0).

  Axiom nat_ext:
    forall {X:Type} {A B:pre X} (n m:natural A B),
    (forall x:X, Id (n x) (m x)) -> Id n m.

  Axiom arr_ext:
    forall {X:Type} {x:X} {A B:pre X},
    forall (f g:A x -> B x),
      (forall y:(A x), Id (f y) (g y)) -> Id f g.
    
  Definition ev_Id {X:Type}
             {A:pre X} {x:X} (n:natural (Id x) A):
    A x := n x (refl x).

  Definition extend_nat {X:Type} {x:X}
             {A:pre X} (z:A x):
    natural (Id x) A := fun (y:X) (f:Id x y) => arr A f z.

  Definition extend_then_ev {X:Type} {x:X} {A:pre X} (z:A x):
    Id (ev_Id (extend_nat z)) z.
  Proof.
    unfold ev_Id. unfold extend_nat. unfold arr.
    simpl. apply refl.
    Defined.
  
  Definition ev_then_nat {X:Type}
             (A: pre X) (x:X) (n: natural (Id x) A):
    Id (extend_nat (ev_Id n)) n.
  Proof.
    apply nat_ext. intros. apply arr_ext. intros.
    unfold extend_nat. unfold ev_Id. unfold arr.
    induction y. simpl. apply refl. Defined.
    
End yoneda.

Section props.

Inductive IsProp (X:Type):=
|isProp (H:forall x0 x1:X, Id x0 x1).

Inductive IsSet (X:Type):=
|isSet (H:forall x0 x1:X, forall p q:Id x0 x1, Id p q).

Axiom funcExt:
  forall X:Type, forall B:X->Type,
  forall H0 H1:forall x:X, B x,
  (forall x:X, Id (H0 x) (H1 x)) -> Id H0 H1.

Definition app {X:Type} {x0 x1:X} (H:X->Type) (K:Id x0 x1):
Id (H x0) (H x1).
Proof.
induction K. apply refl.
Defined.

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

Definition dependentContractibles {X:Type} (B:X->Type):
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


Definition pathsInContractible {X:Type}
  (H0:forall x0 x1:X, Id x0 x1)
  (H1:forall x2 x3:X, Id x2 x3):
  IsContractible X -> Id H0 H1.
Proof.
intro. apply isContractibleImpliesIsSet in X0.
induction X0. apply funcExt. intro. apply funcExt.
intro. induction (H x x0 (H0 x x0) (H1 x x0)).
apply refl.
Defined.



End props.























