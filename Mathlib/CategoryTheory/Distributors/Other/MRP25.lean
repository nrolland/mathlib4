/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator

namespace CategoryTheory.Distributors

@[pp_with_univ]
abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] :=
  Bᵒᵖ × A ⥤ Type u

universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁ } [Category.{v₁} A]
variable {B : Type u₁ } [Category.{v₁} B]
variable {C : Type u₁ } [Category.{v₁} C]
variable {D : Type u₁ } [Category.{v₄} D]


-- Simple product of functors
def timesObj (P : Dist.{u}  A B) (Q: Dist.{v} C D) : (Bᵒᵖ × A) × Dᵒᵖ × C ⥤ Type u × Type v :=
  Functor.prod P Q

-- Not stuck anymore
def timesFunctorFixed : (Dist.{u} A B) × (Dist.{v} C D) ⥤  (Bᵒᵖ × A) × Dᵒᵖ × C ⥤ Type u × Type v    where
  obj := fun (P,Q) ↦ timesObj P Q
  map := sorry

-- But I can't use it timesFunctor.obj
def compObjBAD (P : Dist.{u} A B) (Q: Dist.{v} B C) : (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
  := timesFunctorFixed.obj (P,Q)

-- I can't help the universe solver
def compObjBADD (P : Dist.{u} A B) (Q: Dist.{u} B C) :
    (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type u
  := timesFunctorFixed.obj (P,Q)

-- --Nah
-- def compObjBADDD (P : Dist.{u, v₂, u₂, v₁, u₁} A B) (Q: Dist.{u, v₃,u₃, v₂, u₂} B C) :
--     (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
--   := timesFunctorFixed.obj (P,Q)

--Na
def compObjBadStill (PQ : (Dist.{u} A B) × (Dist.{u} B C)) :
    (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
  := timesFunctorFixed.obj PQ


-- I can use the *definition* of timesFunctor.obj though
def compObjOK (P : Dist A B) (Q: Dist B C) : (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type u
  := timesObj P Q


end CategoryTheory.Distributors
