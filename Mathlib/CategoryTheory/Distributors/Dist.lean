/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Monoidal.Category

namespace CategoryTheory
--namespace CategoryTheory.Functor


-- declare the `v`'s first; see note [CategoryTheory universes].
universe v v₁ v₂ v₃ u u₁ u₂ u₃


structure Distributor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Functor (C ⊗ Dᵒᵖ)   C: Type max v₁ v₂ u₁ u₂



-- instance monoidal : MonoidalCategory (Discrete M) where
--   tensorUnit := Discrete.mk 1
--   tensorObj X Y := Discrete.mk (X.as * Y.as)
--   whiskerLeft X _ _ f := eqToHom (by dsimp; rw [eq_of_hom f])
--   whiskerRight f X := eqToHom (by dsimp; rw [eq_of_hom f])
--   tensorHom f g := eqToHom (by dsimp; rw [eq_of_hom f, eq_of_hom g])
--   leftUnitor X := Discrete.eqToIso (one_mul X.as)
--   rightUnitor X := Discrete.eqToIso (mul_one X.as)
--   associator X Y Z := Discrete.eqToIso (mul_assoc _ _ _)
