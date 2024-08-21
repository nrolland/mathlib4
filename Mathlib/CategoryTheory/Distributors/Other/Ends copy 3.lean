import Mathlib.CategoryTheory.Equivalence

open CategoryTheory

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
set_option linter.longLine false

@[ext]
structure Simple (F : B ⥤ M)  where
  pt : M
  leg c : pt ⟶ F.obj c

structure SimpleMorphism  {F : B ⥤ M} (x y : Simple F) where
  hom : x.pt ⟶ y.pt

variable {F G : B ⥤ M}
variable (i: F ⟶ G)

def fctrObj (i: F ⟶ G) (w: Simple F) : Simple G  where
  pt := w.pt
  leg c := w.leg c ≫ i.app c

def fctrMap {x y} (m : SimpleMorphism x y) : SimpleMorphism (fctrObj i x) (fctrObj i y) :=
  { hom := m.hom }

-- def lawBadTypeMismatch {x y } (m : SimpleMorphism x y ) : (fctrMap (𝟙 F) m) =  m  :=    sorry

def hcast  {x y } : SimpleMorphism x y = SimpleMorphism ((fctrObj (𝟙 F)) x) ((fctrObj (𝟙 F)) y) := by
      congr
      · apply Simple.ext
        · rfl
        · apply heq_iff_eq.mpr
          funext c
          have : (fctrObj (𝟙 F) x).leg c = x.leg c ≫ (𝟙 F: F ⟶ F).app c := rfl
          simp_all only [Category.comp_id, NatTrans.id_app]
      · apply Simple.ext
        · rfl
        · apply heq_iff_eq.mpr
          funext c
          have : (fctrObj (𝟙 F) y).leg c = y.leg c ≫ (𝟙 F: F ⟶ F).app c := rfl
          simp_all only [Category.comp_id, NatTrans.id_app]


def lawGood {x y } (m : SimpleMorphism x y ) : HEq (fctrMap (𝟙 F) m) m  :=
  heq_of_cast_eq (hcast.symm) (by
    have : cast hcast.symm (fctrMap (𝟙 F) m) = m := by
      sorry
    exact this)
