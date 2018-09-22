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

## Deployment 

## Acknowledgements

* [Coq](https://coq.inria.fr/) - Proof Assistant