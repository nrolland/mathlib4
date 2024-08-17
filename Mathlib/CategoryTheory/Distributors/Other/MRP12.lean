/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
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

universe v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory
set_option linter.longLine false

open MonoidalCategory
open CategoryTheory.Bifunctor
open Limits
open Bicategory



section toto
variable {B : Type u₂ } [Category.{u₂} B]
variable {B : Cat.{u₂,u₂}}
def stg : (Functor.hom B).Elements ⥤ Bᵒᵖ × B := CategoryOfElements.π (Functor.hom B)
def stgelse :  Cat.of (Functor.hom B).Elements ⟶ Cat.of (Bᵒᵖ × B) := stg
end toto


section toto

variable {B : Type (u₂+1) } [Category.{u₂} B]
variable {B : Cat.{u₂,u₂+1}}

def extend (F : Bᵒᵖ × B ⥤ Type (u₂+1)) : (Functor.hom B).Elements ⥤ Type (u₂+1)  := CategoryOfElements.π (Functor.hom B) ⋙ F
def colimd (EF : (Functor.hom B).Elements ⥤ Type (u₂+1)): Type (u₂+1) := Limits.colimit EF
def colim_extend (F : Bᵒᵖ × B ⥤ Type (u₂+1)) : Type (u₂+1) := colimd (extend F)


end toto


section precomp
-- making use of
-- Bicategory.precomposing {B : Type u} [Bicategory B] (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c)

variable {B : Type (u₂+1) } [Category.{u₂} B]

def extendok1 := Bicategory.precomposing (Cat.of (Functor.hom B).Elements) (Cat.of (Bᵒᵖ × B)) (Cat.of (Type u₂) : Cat.{u₂,u₂+1})


def precomposingByPi1 : (Bᵒᵖ × B ⥤ Type (u₂)) ⥤ (Functor.hom B).Elements ⥤ Type (u₂)  := extendok1.obj (CategoryOfElements.π (Functor.hom B))
def precomposingByPi : (Bᵒᵖ × B ⥤ Type (u₂)) ⥤ (Functor.hom B).Elements ⥤ Type (u₂) :=
  (Bicategory.precomposing (Cat.of (Functor.hom B).Elements) (Cat.of (Bᵒᵖ × B)) (Cat.of (Type u₂) : Cat.{u₂,u₂+1})).obj
    (CategoryOfElements.π (Functor.hom B))

def colimde (EF : (Functor.hom B).Elements ⥤ Type (u₂+1)): Type (u₂+1) := Limits.colimit EF



end precomp

variable {B : Cat.{u₂,u₂+1}}

noncomputable def coendl : (Bᵒᵖ × B ⥤ Type (u₂+1)) ⥤ (Type (u₂+1)) where
  obj (f : (↑B)ᵒᵖ × ↑B ⥤ Type (u₂ + 1)) := Limits.colimit (extend f)
  map {f g} (n : f ⟶ g) :=
    let n2 : NatTrans (extend f) (extend g) := whiskerLeft (CategoryOfElements.π (Functor.hom B)) n
    (colimit.isColimit (extend f)).desc ( (Cocones.precompose n2).obj (colimit.cocone (extend g)))
  map_id := sorry
  map_comp := sorry


end CategoryTheory
