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

@[ext]
structure SimpleMorphism  {F : B ⥤ M} (x y : Simple F) where
  hom : x.pt ⟶ y.pt

variable {F G : B ⥤ M}
variable (i: F ⟶ G)

def fctrObj (i: F ⟶ G) (w: Simple F) : Simple G  where
  pt := w.pt
  leg c := w.leg c ≫ i.app c


def fctrMap (i: F ⟶ G) {x y} (m : SimpleMorphism x y) : SimpleMorphism (fctrObj i x) (fctrObj i y) :=
  { hom := m.hom } -- FctrMap is essentially the identity

-- I essentially want to prove (fctrMap (𝟙 F) m) =  m, but this is ill-typed
-- def lawBadTypeMismatch {x y } (m : SimpleMorphism x y ) : m = (fctrMap (𝟙 F) m)  :=    sorry

-- So I need HEq
def law {x y } (m : SimpleMorphism x y ) : HEq m (fctrMap (𝟙 F) m)  := sorry

def lawTry {x y } (m : SimpleMorphism x y ) : HEq m (fctrMap (𝟙 F) m)  :=
  heq_of_cast_eq hcast (by
    apply SimpleMorphism.ext
    have result : (cast hcast m).hom  = (fctrMap (𝟙 F) m).hom :=
      have : (fctrMap (𝟙 F) m).hom = m.hom := rfl
      have : (cast hcast m).hom = m.hom  := sorry
      by
      simp_all only
    exact result)

  where
      hcast  {x y } : SimpleMorphism x y = SimpleMorphism ((fctrObj (𝟙 F)) x) ((fctrObj (𝟙 F)) y) := by
        have idobj {x} : x = fctrObj (𝟙 F) x :=  by
          apply Simple.ext
          · rfl
          · apply heq_iff_eq.mpr
            funext c
            have : (fctrObj (𝟙 F) x).leg c = x.leg c ≫ (𝟙 F: F ⟶ F).app c := rfl
            simp_all only [Category.comp_id, NatTrans.id_app]
        congr
        · exact idobj
        · exact idobj
