/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Distributors.End
/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO

## references

- Distributor at work
- Les distributeurs
-/

namespace CategoryTheory.Distributors

set_option linter.longLine false

open CategoryTheory
open MonoidalCategory
open Limits

abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] := Bᵒᵖ × A ⥤ Type u

--- distributors
universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁ } [Category.{v₁} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {D : Type u₄ } [Category.{v₄} D]



def plug : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  := sorry -- Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )

def aassd : ((B × C)ᵒᵖ × (A × B) ⥤ Type u) ⥤ (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤ Type u :=
  (whiskeringLeft _ _  _ ).obj plug



end CategoryTheory.Distributors
