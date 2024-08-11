/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor


namespace CategoryTheory

variable (A B C D : Type*) [Category A] [Category B] [Category C] [Category D]

abbrev Dist := Dᵒᵖ × C ⥤ Type


def times (P : Dist A B) (Q: Dist C D) :  Dist (A × C) (B × D) :=
  let f  : (B × D)ᵒᵖ  ⥤ (A × C)  :=  α
  sorry
