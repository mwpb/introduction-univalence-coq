Section univalence.

  Inductive id {X:Type}:X->X->Type:=
  | refl (x:X): id x x.

  Inductive Preim {X Y:Type} (f:X->Y) (y:Y):=
  |preim (x:X) (H:id (f(x)) y).

  Inductive Eq (X Y:Type):=
  | eq (f:X->Y)
       (inj:forall x0 x1:X, id (f(x0)) (f(x1)) -> id x0 x1)
       (surj: forall y:Y, Preim f y).
  
  Lemma idToEq (X Y:Type):
    id X Y -> Eq X Y.
  Proof.
    intros. induction X0.
    apply (eq x x (fun x0 => x0)).
    - intros. apply X.
    - intros. apply (preim (fun x0 => x0) y y). apply refl.
  Defined.
  
  Axiom univalence:
    forall X Y:Type, isEquiv(idToEq X Y).

  Search existT.

End univalence.