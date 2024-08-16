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

def plugOne : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  := Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )
def plugTwo   : (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤  (B × C)ᵒᵖ × (A × B)  := (prod.inverseAssociator  _ _ _ ) ⋙ Functor.prod (Prod.swap _ _) (𝟭 _) ⋙ Functor.prod (prod.inverseAssociator _ _ _) (𝟭 _) ⋙ (prod.associator  _ _ _ ) ⋙ Functor.prod ((prodOpEquiv B).inverse) (𝟭 _)

def timesObj (P : Dist.{u, v₂, u₂, v₁, u₁} A B) (Q: Dist.{u, v₄,u₄, v₃ , u₃} C D) :
    Dist.{u, (max v₄ v₂), (max u₄ u₂), max v₃ v₁, max u₃ u₁} (A × C) (B × D) :=
  plugOne ⋙ Functor.prod P Q ⋙ tensor (Type u)

def timesFunctor : (Dist.{u, v₂, u₂, v₁, u₁} A B) × ( Dist.{u, v₄,u₄, v₃ , u₃} C D) ⥤
  Dist.{u, (max v₄ v₂), (max u₄ u₂), max v₃ v₁, max u₃ u₁} (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := fun (a,b) ↦ whiskerLeft plugOne (whiskerRight (NatTrans.prod a b) (tensor (Type u)))

def opObj (P : Dist A B) : Dist Bᵒᵖ Aᵒᵖ := (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _) ⋙ P

def op : (Dist A B) ⥤ Dist Bᵒᵖ Aᵒᵖ where
  obj := opObj
  map := whiskerLeft (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _)

def compObj (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  ((whiskeringRight _ _ _ ).obj myCoendPt).obj (curryObj (plugTwo ⋙ timesObj P Q))

def comp : (Dist.{u} A B) × (Dist.{u} B C) ⥤  Dist A C  :=
  timesFunctor ⋙ (whiskeringLeft _ _  _ ).obj plugTwo ⋙ curry ⋙ (whiskeringRight _ _ _ ).obj myCoendPt

end CategoryTheory.Distributors
