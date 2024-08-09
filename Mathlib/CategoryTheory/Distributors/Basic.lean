/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO


## references

- Distributor at work
- Les distributeurs

-/

universe v u
namespace CategoryTheory


variable (A B C D: Cat)


abbrev Dist := Dᵒᵖ × C ⥤ Type


def Prodprod : Type × Type ⥤ Type  := MonoidalCategory.tensor Type

def proasdd (P : Dist A B) (Q: Dist B C) : Cᵒᵖ × C ⥤ Dist A C  :=
  let PtQ := Functor.prod P Q ⋙ MonoidalCategory.tensor Type
  --let PtQ' := sorry
  sorry




def comp (P : Dist A B) (Q: Dist B C) : Dist A C  := sorry






end CategoryTheory
