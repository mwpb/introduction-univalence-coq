Require Coq.Init.Datatypes.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Set Printing Universes.

Section univalence.

  Inductive Id {X:Type}:X->X->Type:=
  |refl (x:X): Id x x.

  Check Id.

  Definition id (X:Type) (x:X):
    X.
  Proof.
    apply x.
  Defined.

  Inductive Preim {X Y:Type} (f:X->Y) (y:Y):=
  |preim (x:X) (H:Id (f(x)) y).

  Inductive IsEq {X Y:Type} (f:X->Y):=
  |isEq (inj:forall x0 x1:X, Id (f(x0)) (f(x1)) -> Id x0 x1)
       (surj:forall y:Y, Preim f y).

  Inductive Eq (X Y:Type):=
  |eq (f:X->Y) (H:IsEq f).
  
  Definition idToEq (X Y:Type):
    Id X Y -> Eq X Y.
  Proof.
    intro. induction X0.
    apply (eq x x (id x)).
    apply isEq.
    - intros. apply X.
    - intros. apply (preim (id x) y y). apply refl.
  Defined.
  
  Axiom univalence:
    forall X Y:Type, IsEq(idToEq X Y).

End univalence.