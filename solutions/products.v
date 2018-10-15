Require Import categorySolutions.
Section products.
  
  Record product {C:caty} (a0 a1:obj C):=
    {prod:>obj C;
     proj_0:hom prod a0;
     proj_1:hom prod a1;
     induced (x:obj C):
       forall f0:hom x a0,
       forall f1:hom x a1,
         hom x prod;
     factorisation {x:obj C} {f0:hom x a0} {f1:hom x a1}:
       comp_hom proj_0 (induced x f0 f1) = f0 /\
       comp_hom proj_1 (induced x f0 f1) = f1;
     uniqueness {x:obj C}:
       forall h k:hom x prod,
         (comp_hom proj_0 h = comp_hom proj_0 k)/\
         (comp_hom proj_1 h = comp_hom proj_1 k)
           -> h = k
    }.

  Arguments induced {C}.
  Arguments prod {C}{a0}{a1}.
  Arguments proj_0 {C}{a0}{a1}.
  Arguments proj_1 {C}{a0}{a1}.

End products.