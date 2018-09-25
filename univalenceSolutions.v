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

  Inductive IsEquiv {X Y:Type} (f:X->Y):=
  |isEquiv (g h:Y->X)
       (H1: forall x:X, Id (g(f(x))) x)
       (H2:forall y:Y, Id (f(h(y))) y).

  Inductive Eq (X Y:Type):=
  |eq (f:X->Y) (H:IsEquiv f).
  
  Definition idToEquiv (X Y:Type):
    Id X Y -> Eq X Y.
  Proof.
    intro. induction X0.
    - apply (eq x x (id x)).
      apply (isEquiv (id x) (id x) (id x)).
      -- intros. unfold id. apply refl.
      -- intros. unfold id. apply refl.
  Defined.
  
  Axiom univalence:
    forall X Y:Type, IsEquiv(idToEquiv X Y).

End univalence.