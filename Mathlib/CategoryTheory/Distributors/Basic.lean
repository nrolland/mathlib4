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

universe v₂ u₂ u
variable {B : Type u₂ } [Category.{v₂} B]

def Functor.ElementsFunctor  : (B ⥤ Type u) ⥤ Cat.{v₂, max u₂ u} where
  obj F := Cat.of.{v₂, max u₂ u} (F.Elements :  Type (max u₂ u) )
  map {F G} n := {
    obj := fun ⟨X,x⟩ ↦  ⟨X, n.app X x ⟩
    map := fun ⟨X, x⟩ {Y} ⟨f,_⟩ ↦
    match Y with | ⟨Y, y⟩ => ⟨f, by have := congrFun (n.naturality f) x;aesop_cat⟩
  }

def mycolimit  : (B ⥤ Type u) ⥤ Type (max u₂ u)
  := @Functor.ElementsFunctor B _ ⋙ Cat.connectedComponents

def mycoend : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B)) ⋙ mycolimit



end mysection_for_coend

namespace CategoryTheory
set_option linter.longLine false

open MonoidalCategory
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


end CategoryTheory
