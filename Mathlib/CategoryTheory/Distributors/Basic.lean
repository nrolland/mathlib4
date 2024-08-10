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
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/

universe v v' v'' v''' u u' u'' u'''
namespace CategoryTheory
set_option linter.longLine false

variable (A: Cat.{v,u}) (B: Cat.{v',u'}) (C: Cat.{v'',u''}) (D: Cat.{v''',u'''})
variable (α β γ)

abbrev Dist := Dᵒᵖ × C ⥤ Type

variable (P : Dist A B)
variable (F : D × C ⥤ Type)


open MonoidalCategory
open CategoryTheory.Bifunctor

def Prodprod : Type × Type ⥤ Type  := tensor Type
-- CategoryTheory.Bifunctor.map_id_comp (F : C × D ⥤ E) (W : C) (f : X ⟶ Y) (g : Y ⟶ Z) : F.map (𝟙 W, f ≫ g) = F.map (𝟙 W, f) ≫ F.map (𝟙 W, g)

def t : B × Cᵒᵖ × A ⥤ (B × Cᵒᵖ) × A := (prod.inverseAssociator  B Cᵒᵖ A)

def tt :  Bᵒᵖ  × (B × (Cᵒᵖ × A)) ⥤  Bᵒᵖ × ((B × Cᵒᵖ) × A)  := Functor.prod (𝟭 Bᵒᵖ) (t A B C )


def ttas : 𝟭 C = 𝟙 C := rfl

def O.{v₂, v₃, v₄, u₂, u₃, u₄} {C : Type u₂} [Category.{v₂, u₂} C] {D : Type u₃} [Category.{v₃, u₃} D]
  {E : Type u₄} [Category.{v₄, u₄} E] (F : C × D ⥤ E) := curryObj F

def proasdd (P : Dist A B) (Q: Dist B C) : Cᵒᵖ × C ⥤ Dist A C  :=
  let PtimesQ : ((↑B)ᵒᵖ × ↑B) × ((↑C)ᵒᵖ × ↑A) ⥤ Type :=
    prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
    Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ prod.inverseAssociator _ _ _  ⋙
    Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type
  let PtimesQ'  := curryObj PtimesQ

  let hom : (↑B)ᵒᵖ × ↑B ⥤ Type v' := CategoryTheory.Functor.hom B

  let p := CategoryTheory.CategoryOfElements.π hom

  let f := p ⋙ PtimesQ'

  sorry




def comp (P : Dist A B) (Q: Dist B C) : Dist A C  := sorry






end CategoryTheory
