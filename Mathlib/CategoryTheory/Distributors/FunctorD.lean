import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.WhiskeringD

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅  u₁ u₂ u₃ u₄ u₅
variable {J : Type u₁} [Category.{v₁} J]
variable {A : Type u₂ } [Category.{v₂} A]
variable {B : Type u₃ } [Category.{v₃} B]
variable {C : Type u₄ } [Category.{v₄} C]
variable {D : Type u₅ } [Category.{v₅} D]

def asFunctorIso  (i: IsoOfCategory B C) : IsoOfCategory (J ⥤ B) (J ⥤ C)  where
  hom  := (whiskeringRight _  _ _ ).obj i.hom
  inv  :=  (whiskeringRight _  _ _ ).obj i.inv
  hom_inv_id :=  by rw [<- whiskeringRight_comp, i.hom_inv_id]; rfl
  inv_hom_id  := by rw [<- whiskeringRight_comp, i.inv_hom_id]; rfl


/-- The cartesian product functor -/
def prodFunctor : (A ⥤ B) × (C ⥤ D) ⥤ A × C ⥤ B × D where
  obj FG := FG.1.prod FG.2
  map nm :=  NatTrans.prod nm.1 nm.2
