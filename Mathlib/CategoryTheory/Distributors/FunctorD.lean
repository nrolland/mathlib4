import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.WhiskeringD

open CategoryTheory

universe v₁ v₂ v₃  u₁ u₂ u₃
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]

def asFunctorIso  (i: IsoOfCategory B C) : IsoOfCategory (J ⥤ B) (J ⥤ C)  where
  hom  := (whiskeringRight _  _ _ ).obj i.hom
  inv  :=  (whiskeringRight _  _ _ ).obj i.inv
  hom_inv_id :=  by rw [<- whiskeringRight_comp, i.hom_inv_id]; rfl
  inv_hom_id  := by rw [<- whiskeringRight_comp, i.inv_hom_id]; rfl
