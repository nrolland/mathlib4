/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator

namespace CategoryTheory.Distributors

open MonoidalCategory

abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] :=
  Bᵒᵖ × A ⥤ Type u

--- distributors
universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁ } [Category.{v₁} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {D : Type u₄ } [Category.{v₄} D]

def plug : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  :=
  Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)
    (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙
      Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )

def timesObj (P : Dist  A B) (Q: Dist  C D) : Dist (A × C) (B × D) :=
  plug ⋙ Functor.prod P Q ⋙ tensor (Type u)

def timesFunctorBAD : (Dist A B) × (Dist C D) ⥤  Dist (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := sorry

def timesFunctor : (Dist.{u, v₂, u₂, v₁, u₁} A B) × (Dist.{u, v₄,u₄, v₃ , u₃} C D) ⥤
  Dist.{u, (max v₄ v₂), (max u₄ u₂), max v₃ v₁, max u₃ u₁} (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := sorry

def compObjOK (P : Dist A B) (Q: Dist B C) : Dist (A × B) (B × C)  := timesObj P Q

def compObjBAD (P : Dist A B) (Q: Dist B C) : Dist (A × B) (B × C)
  := timesFunctor.obj (P,Q)

def compObjBADD (P : Dist.{u, v₂, u₂, v₁, u₁} A B) (Q: Dist.{u, v₃,u₃, v₂, u₂} B C) :
    Dist.{u, (max v₃ v₂), (max u₃ u₂), max v₂ v₁, max u₂ u₁} (A × B) (B × C)
  := timesFunctor.obj (P,Q)

def compObjBADDD (P : Dist.{u, v₂, u₂, v₁, u₁} A B) (Q: Dist.{u, v₃,u₃, v₂, u₂} B C) :
    Dist.{u, (max v₃ v₂), (max u₃ u₂), max v₂ v₁, max u₂ u₁} (A × B) (B × C)
  := timesFunctor.obj (P,Q)


end CategoryTheory.Distributors
