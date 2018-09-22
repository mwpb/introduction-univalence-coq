(* intros. induction X0. *)
(*     apply (eq x x (fun x0 => x0)). *)
(*     - intros. apply isEq. *)
(*       -- intros. apply X. *)
(*       -- intros. apply (preim (fun x0 => x0) y y). *)
(*          apply refl. *)


  Definition idToEq (X Y:Type):
    Id X Y -> Eq X Y.
  Proof.
    intro. induction X0.
    apply (eq x x (id x)).
    apply isEq.
    - intros. apply X.
    - intros. apply (preim (id x) y y). apply refl.
  Defined.