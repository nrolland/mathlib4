import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.EqToHomD
import Mathlib.CategoryTheory.Distributors.WhiskeringD

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um w
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]

def asEmptyConeMorphism {x y : C} (f : x ⟶ y) :
    Limits.ConeMorphism (Limits.asEmptyCone x) (Limits.asEmptyCone y) :=
    { hom := f }

abbrev Terminal (B : Type u₂ ) [Category.{v₂} B] :=  Σ x : B, IsTerminal x
instance terminalGroupoid : Groupoid (Terminal B) where
  Hom x y  :=  x.1 ⟶ y.1
  id x := 𝟙 x.1
  comp {x y z} f g :=  f ≫ g
  inv {x y} _  :=  IsTerminal.from x.2 y.1
  inv_comp {_ y} _ := IsTerminal.hom_ext y.2 _ _
  comp_inv {x _} _ := IsTerminal.hom_ext x.2 _ _
def terminalConnected (x y : Terminal B) : x ⟶ y := Limits.IsTerminal.from y.2 x.1

theorem uniq_morphism_to_terminal {s t : B} (h : IsTerminal t) {f f' : s ⟶ t} : f = f' :=
  congrArg ConeMorphism.hom (uniq_cone_morphism h : asEmptyConeMorphism f = asEmptyConeMorphism f')

def asFunctorIso  (i: IsoOfCategory B C) : IsoOfCategory (J ⥤ B) (J ⥤ C)  where
  hom  := (whiskeringRight _  _ _ ).obj i.hom
  inv  :=  (whiskeringRight _  _ _ ).obj i.inv
  hom_inv_id :=  by rw [<- whiskeringRight_comp, i.hom_inv_id]; rfl
  inv_hom_id  := by rw [<- whiskeringRight_comp, i.inv_hom_id]; rfl

  -- IsoOfCategory (Discrete.{w} PEmpty ⥤  B) (Discrete.{w} PEmpty ⥤ C) := asFunctorIso i
