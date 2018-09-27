# Introduction to univalence in Coq

Some exercises leading up to the formulation of the univalence axiom using the Coq proof assistant.

Files ending in *Solution.v contain proofs; other *.v files have the proofs removed.

## Getting started

Install Coq [here](https://coq.inria.fr/).

If developing in emacs place the following lines:

```
(setq coq-load-path-include-current t)
(setq coq-compile-before-require t)
```

in your init file.
If not then you may have to run coqc on the various dependencies to run the proofs.
For instance in CoqIde (which is automatically installed alongside Coq) you may need to do

```
Compile > Compile buffer
```

on any files that Coq has trouble loading. 
Hopefully the addition of a line in [\_CoqProject](_CoqProject) has taken care of LoadPath issues. 
If not please try the solution suggested [here](https://stackoverflow.com/questions/16202666/coqide-cant-load-modules-from-same-folder).

## Intended order of files

1. [inductionAndFunctions.v](inductionAndFunctions.v) introduces the Inductive and Definition keywords as well as the induction, destruct and apply tactics.
2. [lemmas.v](lemmas.v) introduces proofs as programmes and the simpl and rewrite tactics.
3. [univalence.v](univalence.v) formulates the univalence axiom.
4. [productStrictlyAssoc.v](productStrictlyAssoc.v) uses the univalence axiom to prove that the product type construction is strictly associative in the appropriate sense.


## Acknowledgements

* [Coq](https://coq.inria.fr/) - Proof Assistant
* The HoTT book - available [here](https://homotopytypetheory.org/book/)
* [Using Yoneda rather than J to present the identity type](http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html) - Martin Escardo
* [A self-contained, brief and complete formulation of Voevodsky's univalence Axiom](http://www.cs.bham.ac.uk/~mhe/agda-new/UnivalenceFromScratch.html) - Martin Escardo
