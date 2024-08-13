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

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/


universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory
set_option linter.longLine false


variable (X : Type u ) [Category.{v} X]
variable (A : Type u₁ ) [Category.{u₁+1} A]
variable {B : Type u₂ } [Category.{u₂+1} B]
variable (C : Type u₃ ) [Category.{u₃+1} C]
variable (D : Type u₄ ) [Category.{v₄} D]

abbrev Dist := Dᵒᵖ × C ⥤ Type

variable (P : Dist A B)
variable (F : D × C ⥤ Type)

open MonoidalCategory
open CategoryTheory.Bifunctor
open Limits




def mycolimit : (X ⥤ Type u) ⥤  Type u := sorry


-------
def times (P : Dist A B) (Q: Dist C D) :  Dist (A × C) (B × D) :=
  let plug  : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  :=
    Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙
    Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙
     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙
    (prod.inverseAssociator  _ _ _ )
  plug ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type

def op (P : Dist A B) :  Dist Bᵒᵖ Aᵒᵖ :=
  let plug  : (Aᵒᵖ)ᵒᵖ  × Bᵒᵖ ⥤ Bᵒᵖ × A := Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _
  plug ⋙ P

def extend (F : Bᵒᵖ × B ⥤ Type (u₂+1)) : (Functor.hom B).Elements ⥤ Type (u₂+1)  :=
  CategoryOfElements.π (Functor.hom B) ⋙ F

noncomputable def coendl : (Bᵒᵖ × B ⥤ Type (u₂+1)) ⥤ (Type (u₂+1)) where
  obj (f : Bᵒᵖ × B ⥤ Type (u₂ + 1)) := Limits.colimit (extend f)
  map {f g} (n : f ⟶ g) :=
      (colimit.isColimit (extend f)).desc
        ((Cocones.precompose (whiskerLeft (CategoryOfElements.π (Functor.hom B)) n)).obj
         (colimit.cocone (extend g)))
  map_id := sorry
  map_comp := sorry


def comp (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  let PtimesQ : ((↑B)ᵒᵖ × ↑B) × (Cᵒᵖ × A) ⥤ Type :=
    prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
    Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ prod.inverseAssociator _ _ _  ⋙
    Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type

  let mynicefunctor : (Functor.hom B).Elements ⥤ Cᵒᵖ × A ⥤ Type := CategoryOfElements.π (CategoryTheory.Functor.hom B) ⋙ curryObj PtimesQ
  let myotherfunctor : (Functor.hom B).Elements ⥤ Cᵒᵖ × A ⥤ Type := CategoryOfElements.π (CategoryTheory.Functor.hom B) ⋙ curryObj PtimesQ

  let ok1 := Limits.colimit (CategoryOfElements.π (Functor.hom B) ⋙ Functor.hom B)
  let sad := Limits.colimit (CategoryOfElements.π (Functor.hom B) ⋙ Functor.hom B)
  sorry




end CategoryTheory
