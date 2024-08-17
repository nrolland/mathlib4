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

open CategoryTheory

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)

structure CoWedge (F : (Bᵒᵖ×B) ⥤ M) where
  pt : M
  leg (b:B) : F.obj (Opposite.op b,b) ⟶ pt
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (F.map ((𝟙 c').op, f) ≫ leg c'  : F.obj (Opposite.op c', c)  ⟶  pt)
     = (F.map (f.op, 𝟙 c) ≫ leg c : F.obj (Opposite.op c', c) ⟶  pt)  := by aesop_cat

structure CoWedgeMorphism (x y : CoWedge F) where
  Hom : x.pt ⟶ y.pt
--  cowedgeCondition : ∀ (c : B), y.leg c  = x.leg c ≫ Hom  := by aesop_cat
  cowedgeCondition : ∀ (c : B), y.leg c  = x.leg c ≫ Hom  := by aesop_cat

attribute [simp] CoWedgeMorphism.cowedgeCondition

-- The category of Cowedges
instance : Category (CoWedge F) where
  Hom := fun x y => CoWedgeMorphism _ x y
  id := fun x => {Hom := 𝟙 x.pt}
  comp := fun {X Y Z} f g => {
    Hom := f.Hom ≫ g.Hom
    -- cowedgeCondition := fun c  => by
    --                        rw [<- Category.assoc, g.cowedgeCondition c, f.cowedgeCondition c];
      -- have ha : Y.leg c = X.leg c ≫ f.Hom := f.cowedgeCondition c ;
      -- have hb : Z.leg c = Y.leg c ≫ g.Hom := g.cowedgeCondition c ;
      -- have hc : (X.leg c ≫ f.Hom) ≫ g.Hom = X.leg c ≫ (f.Hom ≫ g.Hom) := by rw [<- Category.assoc];
      -- have : Z.leg c = X.leg c ≫ f.Hom ≫ g.Hom:= hc ▸ ha ▸ hb ▸ rfl ;
      }
  --comp := fun f g => { Hom := f.Hom ≫ g.Hom, cowedgeCondition := fun c => sorry}

def myCoendType  (F : Bᵒᵖ × B ⥤ Type u) : Type (max u₂ u) :=  Σb : B, F.obj (Opposite.op b,b)

def myCoend (F : Bᵒᵖ × B ⥤ Type (max u₂ u)) : CoWedge F  where
  pt := myCoendType F
  leg := sorry
  wedgeCondition := sorry
