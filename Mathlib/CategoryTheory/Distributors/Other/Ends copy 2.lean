import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory
open CategoryOfElements
open Functor
open Opposite

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)
set_option linter.longLine false

@[ext]
structure Wedge (F : (Bᵒᵖ×B) ⥤ M): Type (max (max um u₂) vm) where
  pt : M

@[ext]
structure WedgeMorphism  {F : (Bᵒᵖ×B) ⥤ M} (x y : Wedge F) where
  hom : x.pt ⟶ y.pt

instance : Category (Wedge F) where
  Hom x y:=  WedgeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

def wedgeFctrHom {F G : (Bᵒᵖ×B) ⥤ M} (i: F ⟶ G) : Wedge F ⥤ Wedge G  where
  obj w :=  { pt := w.pt }
  map {X Y} m := { hom := m.hom}

lemma wedgeFctrHomIdObj (x : Wedge F): ((wedgeFctrHom (𝟙 F)).obj x) = x := by
    apply Wedge.ext
    · dsimp;rfl

def wedgeFctr : (Bᵒᵖ×B ⥤ M) ⥤ Cat where
  obj f := Cat.of (Wedge f )
  map {f g } α := wedgeFctrHom α
  map_id f := by
    dsimp -- Wedge F ⥤ Wedge F = 𝟙 (Wedge F)
    apply CategoryTheory.Functor.hext
    · intro x -- objets
      exact wedgeFctrHomIdObj f x
    · intro x y m -- morphismes de wedge vers morphisme de wedge = id
      dsimp
      let as : x ⟶ y := eqToHom ((wedgeFctrHomIdObj f x).symm) ≫ (wedgeFctrHom (𝟙 f)).map m ≫ eqToHom (wedgeFctrHomIdObj f y)

      let hcast : (x ⟶ y) = ((wedgeFctrHom (𝟙 f)).obj x ⟶ (wedgeFctrHom (𝟙 f)).obj y) := by
        congr

      let asqw := cast hcast m
      let qsqrw := asqw.hom
      have asdq : asqw.hom = m.hom := by      simp_all only [cast_eq, asqw]

      let asqwq : (wedgeFctrHom (𝟙 f)).map m = asqw := by
        apply WedgeMorphism.ext
        aesop

      --HEq x:a y:b  equiv  cast x (a = b) = y : b
      let goal := HEq ((wedgeFctrHom (𝟙 f)).map m) m
      aesop?
  map_comp := sorry
