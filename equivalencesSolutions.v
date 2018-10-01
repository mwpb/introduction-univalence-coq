Require Import Coq.Init.Datatypes.
Require Import Coq.Program.Tactics.
Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.

Section equivalences.

  Inductive Id {X:Type}:X->X->Type:=
  |refl (x:X): Id x x.

  Check Id.

  Definition id (X:Type) (x:X):
    X.
  Proof.
    apply x.
  Defined.

  Definition appl {X Y:Type} {x0 x1:X} (f:X->Y) (n: Id x0 x1):
    Id (f(x0)) (f(x1)).
  Proof.
    induction n. apply refl.
  Defined.

  Inductive Qinv {X Y:Type} (f:X->Y):=
  |qinv (g:Y->X)
        (n:forall x:X, Id (g(f(x))) x)
        (e:forall y:Y, Id (f(g(y))) y).

  Inductive Biinv {X Y:Type} (f:X->Y):=
  |biinv  (g h:Y->X)
          (n:forall x:X, Id (g(f(x))) x)
          (e:forall y:Y, Id (f(h(y))) y).
            
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

  Inductive Linv {X Y:Type} (f:X->Y):=
    |linv (g:Y->X) (H:forall x:X, Id (g(f(x))) x).

  Inductive Rinv {X Y:Type} (f:X->Y):=
  |rinv (g:Y->X) (H:forall y:Y, Id (f(g(y))) y).
  
End equivalences.