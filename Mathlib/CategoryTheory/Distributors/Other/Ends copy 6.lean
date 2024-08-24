import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom

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
structure SimpleMorphism {F : B ⥤ M} (x y : Simple F) where
  hom : x.pt ⟶ y.pt

instance {F : B ⥤ M} : Category (Simple F) where
  Hom := SimpleMorphism
  id x := ⟨𝟙 x.pt⟩
  comp f g := ⟨f.hom ≫ g.hom⟩

variable {F G : B ⥤ M}
variable (i : F ⟶ G)

def fctrObj (i: F ⟶ G) (x: Simple F) : Simple G  where
  pt := x.pt
  leg c := x.leg c ≫ i.app c

def fctrMap (i: F ⟶ G) {x y : Simple F} (m : x ⟶ y) : fctrObj i x ⟶ fctrObj i y :=
  { hom := m.hom }

lemma hom_comp {x y z : Simple F} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

lemma hom_eqToHom {x x' : Simple F} (h : x = x') : (eqToHom h).hom = eqToHom (by rw [h]) := by
  cases h; rfl

lemma id_fctrObj {x : Simple F} : x = fctrObj (𝟙 F) x := by simp [fctrObj]

def law {x y : Simple F} (m : x ⟶ y) :
    m = eqToHom id_fctrObj ≫ (fctrMap (𝟙 F) m) ≫ eqToHom (id_fctrObj.symm) := by
  apply SimpleMorphism.ext
  simp [fctrMap, hom_comp, hom_eqToHom]

def law' {x y : Simple F} (m : x ⟶ y) : HEq m (fctrMap (𝟙 F) m) :=
    (Functor.conj_eqToHom_iff_heq m (fctrMap (𝟙 F) m) (by simp [fctrObj]) (by simp [fctrObj]) ).mp (law m)
