import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

universe v u
variable {C D : Cat.{u,v}}
variable (F G : C ⥤ D)

set_option trace.aesop true
set_option trace.aesop.proof true

def usingFunctorEq  ( h : F = G)  : F = G  := show_term by
  fapply Functor.ext
  . subst h
    simp
  . intro X Y f
    rewrite [h]
    simp

def usingFunctorEq2  (h : F = G)  : F = G := show_term by
  fapply Functor.ext
  · subst h
    simp
  · intro X Y f
    subst h
    simp
