Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Print LoadPath.
Require Import equivalencesDefinitions.

Section equivalences.

Definition halfAdjointImpliesQinv {X Y:Type} (f:X->Y):
HalfAdjointEquiv f -> Qinv f.
Proof.
intro p. induction p. apply (qinv f g).
- apply n.
- apply e.
Defined.

Definition qinvImpliesHalfAdjoint {X Y:Type} (f:X->Y):
Qinv f -> HalfAdjointEquiv f.
Proof.
intro q.
induction q.
apply (halfAdjointEquiv f g n e).
intro.
specialize n with x as n0.
specialize e with (f x) as e0.
Admitted.
          
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

Definition qinvImpliesBiinv {X Y:Type} (f:X->Y):
  Qinv f -> Biinv f.
Proof.
intro q. induction q. apply (biinv f g g).
- apply n.
- apply e.
Defined.

Definition invOfContractibleMap {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  Y->X.
Proof.
intro y. induction H. induction (K y). apply x.
Defined.

Definition invIsSection {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  forall y:Y, Id (f(invOfContractibleMap f H y)) y.
Proof.
intro. induction H. simpl. induction (K y).
simpl. apply H0.
Defined.

Definition invIsRetraction {X Y:Type} 
  (f:X->Y) (H:IsContractibleMap f):
  forall x:X, Id (invOfContractibleMap f H (f x)) x.
Proof.
intro. induction H. induction (K (f x)).
apply H.
- apply (f x).
- apply invIsSection.
Defined.

Definition isContractibleMapImpliesQinv {X Y:Type} (f:X->Y):
IsContractibleMap f -> Qinv f.
Proof.
intro. induction X0.
apply (qinv f (invOfContractibleMap f (isContractibleMap f H K))).
- apply invIsRetraction.
- apply invIsSection.
Defined.
  
End equivalences.