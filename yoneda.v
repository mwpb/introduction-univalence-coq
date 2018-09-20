Section yoneda.
  (* Requirements: 
   1. induction tactic
   2. apply tactic
   3. unfold tactic
   4. simpl tactic*)
  
  Inductive id {X}:X->X->Type:=
  | refl (x:X): id x x.
  
  Definition pre (X:Type):= X->Type.
  
  Definition arr {X:Type} {x y:X}
             (A:pre X) (f:id x y):
    (A x) -> (A y).
  Proof.
    induction f. apply (fun x => x). Defined.
    
  Definition natural {X:Type} (A B:pre X):Type:=
    forall x0:X, (A x0) -> (B x0).

  Axiom nat_ext:
    forall {X:Type} {A B:pre X} (n m:natural A B),
    (forall x:X, id (n x) (m x)) -> id n m.

  Axiom arr_ext:
    forall {X:Type} {x:X} {A B:pre X},
    forall (f g:A x -> B x),
      (forall y:(A x), id (f y) (g y)) -> id f g.
    
  Definition ev_id {X:Type}
             {A:pre X} {x:X} (n:natural (id x) A):
    A x := n x (refl x).

  Definition extend_nat {X:Type} {x:X}
             {A:pre X} (z:A x):
    natural (id x) A := fun (y:X) (f:id x y) => arr A f z.

  Lemma extend_then_ev {X:Type} {x:X} {A:pre X} (z:A x):
    id (ev_id (extend_nat z)) z.
  Proof.
    unfold ev_id. unfold extend_nat. unfold arr.
    simpl. apply refl. Qed.
  
  Lemma ev_then_nat {X:Type}
        (A: pre X) (x:X) (n: natural (id x) A):
    id (extend_nat (ev_id n)) n.
  Proof.
    apply nat_ext. intros. apply arr_ext. intros.
    unfold extend_nat. unfold ev_id. unfold arr.
    induction y. simpl. apply refl. Defined.
    
End yoneda.
