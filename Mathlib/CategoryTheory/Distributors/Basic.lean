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

universe v u
namespace CategoryTheory
set_option linter.longLine false

variable (A B C D: Cat)
variable (α β γ)

abbrev Dist := Dᵒᵖ × C ⥤ Type

namespace hide

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
  deriving Repr

namespace Vector

def map2 (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map2 f as bs)

end Vector

end hide


def Prodprod : Type × Type ⥤ Type  := MonoidalCategory.tensor Type

def proasdd (P : Dist A B) (Q: Dist B C) : Cᵒᵖ × C ⥤ Dist A C  :=
  let PtimesQ  := Functor.prod P Q ⋙ MonoidalCategory.tensor Type
  let plug : (Bᵒᵖ × ↑B) × (Cᵒᵖ× A) ⥤  (Bᵒᵖ × A) × (Cᵒᵖ × B) :=  sorry -- by coherence
  let PtimesQ' := plug ⋙ PtimesQ
  sorry




def comp (P : Dist A B) (Q: Dist B C) : Dist A C  := sorry






end CategoryTheory
