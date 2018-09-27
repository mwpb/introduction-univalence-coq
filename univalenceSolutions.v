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

  (* Inductive IsProp (X:Type) := *)
  (* |isProp (H:forall x y:X, Id x y). *)

  (* Inductive IsContractible (X:Type) := *)
  (* |isContractible (x:X) (H:IsProp X). *)

  (* Inductive Fibre {X Y:Type} (f:X->Y) (y:Y) := *)
  (* |fibre (x:X) (H: Id (f(x)) y). *)

  (* Inductive IsEquiv {X Y:Type} (f:X->Y) := *)
  (* |isEquiv (H:forall y:Y, IsContractible (Fibre f y)). *)

  (* Inductive Equiv (X Y:Type) := *)
  (* |equiv (f:X->Y) (H:IsEquiv f). *)

  (* Definition idToEquiv (X Y:Type): *)
  (*   Id X Y -> Equiv X Y. *)
  (* Proof. *)
  (*   intros. induction X0. apply (equiv x x (id x)). *)
  (*   apply isEquiv. intros. apply isContractible. *)
  (*   - apply (fibre (id x) y y). unfold id. apply refl. *)
  (*   - apply isProp. intros. induction x0, y0. *)
  (*     unfold id in H. unfold id in H0. induction H. induction H0. apply refl. *)
  (* Defined. *)

  Inductive IsEquiv {X Y:Type} (f:X->Y):=
  |isEquiv (g h:Y->X)
       (H1: forall x:X, Id (g(f(x))) x)
       (H2:forall y:Y, Id (f(h(y))) y).

  Inductive Equiv (X Y:Type):=
  |eq (f:X->Y) (H:IsEquiv f).
  
  Definition idToEquiv (X Y:Type):
    Id X Y -> Equiv X Y.
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