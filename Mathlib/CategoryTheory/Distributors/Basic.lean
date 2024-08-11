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
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/

universe v v' v'' v''' u u' u'' u''' w
namespace CategoryTheory
set_option linter.longLine false

variable (A B C D : Type*) [Category A] [Category B] [Category C] [Category D]

abbrev Dist := Dᵒᵖ × C ⥤ Type

variable (P : Dist A B)
variable (F : D × C ⥤ Type)

open MonoidalCategory
open CategoryTheory.Bifunctor

-- def composition (P : Dist A B) (Q: Dist B C) :  Dist A C  :=
--   let PtimesQ : ((↑B)ᵒᵖ × ↑B) × ((↑C)ᵒᵖ × ↑A) ⥤ Type :=
--     prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
--     Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ prod.inverseAssociator _ _ _  ⋙
--     Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type
--   let PtimesQ'  := curryObj PtimesQ
--   let Bhom : (↑B)ᵒᵖ × ↑B ⥤ Type v' := CategoryTheory.Functor.hom B
-- noncomputable example := Functor.leftKanExtension oneL oneX
-- noncomputable example := Functor.pointwiseLeftKanExtension oneL oneX
--   let comp := Functor.leftKanExtension (Functor.star Bhom.Elements) (CategoryOfElements.π Bhom ⋙ PtimesQ')
--   comp.obj (⟨PUnit.unit⟩)


def times (P : Dist A B) (Q: Dist C D) :  Dist (A × C) (B × D) :=
  let a := Functor.prod P Q ⋙ MonoidalCategory.tensor Type
  let f  : (B × D)ᵒᵖ  × (A × C)    ⥤ (Bᵒᵖ × Dᵒᵖ) × (A × C)  :=  sorry
  let fg : (Bᵒᵖ × Dᵒᵖ) × (A × C)   ⥤  Bᵒᵖ × (Dᵒᵖ × (A × C))  := sorry
  let fg :  Bᵒᵖ × (Dᵒᵖ × (A × C))  ⥤  Bᵒᵖ × ((Dᵒᵖ × A) × C) := sorry
  let fg :  Bᵒᵖ × ((Dᵒᵖ × A) × C)  ⥤  Bᵒᵖ × (( A × Dᵒᵖ) × C) := sorry
  let fg :  Bᵒᵖ × (( A × Dᵒᵖ) × C) ⥤  Bᵒᵖ × ( A × (Dᵒᵖ × C))  := sorry
  let fg :  Bᵒᵖ × ( A × (Dᵒᵖ × C)) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C := sorry
  sorry

def op (P : Dist A B) :  Dist Bᵒᵖ Aᵒᵖ := sorry


-- a la main avec equivalence ?
-- pour object, pour map, etc..
def comp (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  let Bhom : (↑B)ᵒᵖ × ↑B ⥤ Type v' := CategoryTheory.Functor.hom B
  {
    obj := sorry
    map := sorry
  }




end CategoryTheory
