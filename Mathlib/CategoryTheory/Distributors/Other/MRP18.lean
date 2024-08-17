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

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/


section sthg

open CategoryTheory

universe u
universe v₂ u₂
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

def myprecomp  : (Bᵒᵖ × B ⥤ Type u) ⥤  (Functor.hom B).Elements ⥤ Type u :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B))

def mycoend : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) :=  myprecomp ⋙ mycolimit


end sthg
