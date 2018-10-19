Require Import univalenceSolutions.

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
    (Id a b) -> iso a b.
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
      IsEquiv(idToIso a b).

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

