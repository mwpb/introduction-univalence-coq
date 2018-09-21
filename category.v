Section category.

  Record caty:=
    {obj:Type;
     arr:Type;
     s:arr->obj;
     t:arr->obj;
     e:obj->arr;
     t_section:
       forall x:obj,
         t(e(x)) = x;
     s_section:
       forall x:obj,
         x = s(e(x));
     comp:
       forall g f:arr,
         t(f)=s(g) -> arr;
     s_comp:
       forall g f:arr,
       forall H:t(f)=s(g),
         s(f) = s(comp g f H);
     t_comp:
       forall g f:arr,
       forall H:t(f)=s(g),
         t(comp g f H) = t(g);
     left_id:
       forall g:arr, forall m:obj,
           forall H:t(e(m)) = s(g),
           comp g (e(m)) H = g;
     right_id:
       forall g:arr, forall m:obj,
           forall H:t(g) = s(e(m)),
             comp (e(m)) g H = g;
     assoc:
       forall h g f:arr,
       forall H:t(f)=s(g),
       forall K:t(g)=s(h),
         comp (comp h g K) f (eq_trans H (s_comp h g K)) = comp h (comp g f H) (eq_trans (t_comp g f H) K)
    }.

  Arguments t {c}.
  Arguments s {c}.
  Arguments e {c}.
  Arguments comp {c}.
  Arguments t_section {c}.
  Arguments s_section {c}.
  Arguments s_comp {c}.
  Arguments t_comp {c}.
  Arguments left_id {c}.
  Arguments right_id {c}.
  Arguments assoc {c}.

  Record hom {C:caty} (a b:obj C):=
    {arrow:>arr C;
     source:(s(arrow)=a);
     target:(t(arrow)=b)}.

  Lemma s_hom {C:caty} {a b:obj C} (f:hom a b):
    s(f) = a.
  Proof.
    apply source. Defined.

  Lemma t_hom {C:caty} {a b:obj C} (f:hom a b):
    t(f) = b.
  Proof.
    apply target. Defined.

  Definition comp_hom {C:caty} {a b c:obj C}
             (g:hom b c) (f:hom a b):arr C.
  Proof.
    apply (comp g f). rewrite t_hom. rewrite s_hom. reflexivity.
    Defined.

  Definition isIso {C:caty} (f:arr C):=
    exists g:arr C, exists (H:t(f)=s(g)), exists (K:t(g)=s(f)),
          (comp g f H) = e(s(f)) /\ (comp f g K) = e(s(g)).

  Definition iso {C:caty} (a b:obj C):=
    exists f:arr C,
      (s(f) = a)/\(t(f) = b)/\(isIso f).

  Lemma idToIso {C:caty} (a b:obj C):
    id a b -> iso a b.
  Proof.
    intros. unfold iso. induction X. exists (e(x)).
    split.
    - apply eq_sym. apply s_section.
    - split.
      -- apply t_section.
      -- unfold isIso. exists (e(x)).
         exists (eq_trans (t_section x) (s_section x)).
         exists (eq_trans (t_section x) (s_section x)).
         split.
         --- rewrite (s_section x). rewrite left_id.
             rewrite <- s_section. rewrite <- s_section.
             reflexivity.
         --- rewrite (s_section x). rewrite left_id.
             rewrite <- s_section. rewrite <- s_section.
             reflexivity.
  Defined.

  Axiom caty_univalence:
    forall {C:caty} (a b:obj C),
      isEquiv(idToIso a b).

End category.

Arguments t {c}.
Arguments s {c}.
Arguments e {c}.
Arguments comp {c}.
Arguments t_section {c}.
Arguments s_section {c}.
Arguments s_comp {c}.
Arguments t_comp {c}.
Arguments left_id {c}.
Arguments right_id {c}.
Arguments assoc {c}.

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

  Lemma all_products_iso {C:caty} (a0 a1:obj C):
    forall X Y: product a0 a1,
      iso (prod X) (prod Y).
  Proof.
    intros. unfold iso. exists (induced (prod X) (proj_0 X) (proj_1 X)).
    
    
    
    
    