import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory
open Functor
open Opposite

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)
set_option linter.longLine false

@[ext]
structure Simple (F : B ⥤ M)  where
  pt : M
  -- leg c : pt ⟶ F.obj c

@[ext]
structure SimpleMorphism  {F : B ⥤ M} (x y : Simple F) where
  hom : x.pt ⟶ y.pt

variable {F G : (Bᵒᵖ×B) ⥤ M}

def fctrObj (i: F ⟶ G) (w: Simple F) : Simple G  where
  pt := w.pt
  -- leg c := w.leg c ≫ i.app c

def fctrHomMap  (i: F ⟶ G) {x y}  (m : SimpleMorphism x y) : SimpleMorphism (fctrObj i x) (fctrObj i y) :=
  { hom := m.hom }


def law   {x y } (m : SimpleMorphism x y ) : HEq (fctrHomMap (𝟙 F) m) m  :=
    let hcast : SimpleMorphism x y = SimpleMorphism ((fctrObj (𝟙 F)) x) ((fctrObj (𝟙 F)) y) := sorry
    let cm := cast hcast m
    have asdq : cm.hom = m.hom := by aesop?
    sorry
