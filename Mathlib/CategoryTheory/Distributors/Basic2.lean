/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/

section mysection_for_coend

open CategoryTheory

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)


structure Wedge  where
  pt : M
  leg (b:B) : pt ⟶ F.obj (Opposite.op b,b)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (Opposite.op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (Opposite.op c, c'))  := by aesop_cat

structure WedgeMorphism (x y : Wedge F) where
  Hom : x.pt ⟶ y.pt
  wedgeCondition : ∀ (c : B), Hom ≫ y.leg c = x.leg c  := by aesop_cat

attribute [simp] WedgeMorphism.wedgeCondition

-- The category of Wedges
instance  (F : (Bᵒᵖ×B) ⥤ M) : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism _ x y
  id := fun x => {Hom := 𝟙 x.pt}
  comp := fun f g => { Hom := f.Hom ≫ g.Hom }

def myCoendType  (F : Bᵒᵖ × B ⥤ Type u) :  Type _  := Σb : B, F.obj (Opposite.op b,b)

def myCoend  (F : Bᵒᵖ × B ⥤ Type u)  : Wedge F  where
  pt := myCoendType F
  leg := sorry
  wedgeCondition := sorry


--instance  (F : Bᵒᵖ × B ⥤ Type u)  : IsTerminal (myCoEnd F : _ ) where := sorry

end mysection_for_coend

namespace CategoryTheory
set_option linter.longLine false

open MonoidalCategory
open CategoryTheory.Bifunctor
open Limits

abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] := Bᵒᵖ × A ⥤ Type u

--- distributors
universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁ } [Category.{v₁} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {D : Type u₄ } [Category.{v₄} D]

def times (P : Dist.{u} A B) (Q: Dist.{u} C D) :  Dist.{u} (A × C) (B × D) :=
  let plug  : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  :=
    Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙
    Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙
     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙
    (prod.inverseAssociator  _ _ _ )
  plug ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor (Type u)

def op (P : Dist.{u} A B) :  Dist.{u} Bᵒᵖ Aᵒᵖ :=
  let plug  : (Aᵒᵖ)ᵒᵖ  × Bᵒᵖ ⥤ Bᵒᵖ × A := Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _
  plug ⋙ P

---
def comp (P : Dist.{u} A B) (Q: Dist.{u} B C) : Dist.{max u u₂ v₂} A C  :=
  let plug :  (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤   (B × C)ᵒᵖ × (A × B)  := (prod.inverseAssociator  _ _ _ ) ⋙ Functor.prod (Prod.swap _ _) (𝟭 _) ⋙ Functor.prod (prod.inverseAssociator _ _ _) (𝟭 _) ⋙ (prod.associator  _ _ _ ) ⋙ Functor.prod ((prodOpEquiv B).inverse) (𝟭 _)
  let pq : Cᵒᵖ × A ⥤ Bᵒᵖ × B ⥤ Type u := curryObj (plug ⋙ times P Q)

  let that_increase_universe : ((Cᵒᵖ × A) ⥤ (Bᵒᵖ × B ⥤ Type u)) ⥤ ((Cᵒᵖ × A) ⥤  Type (max u u₂ v₂)) := (CategoryTheory.whiskeringRight _ _ _ ).obj mycoend

  that_increase_universe.obj pq


-- CategoryTheory.Functor.{v₁, v₂, u₁, u₂} (C : Type u₁) [Category.{v₁, u₁} C] (D : Type u₂) [Category.{v₂, u₂} D] :  Type (max v₁ v₂ u₁ u₂)

def asdascomp (F : A  ⥤ B) (G : B ⥤ C) : A ⥤ C where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_comp := by intros; dsimp; rw [F.map_comp, G.map_comp]


end CategoryTheory
