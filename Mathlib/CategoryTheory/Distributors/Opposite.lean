/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Distributors.End
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Distributors.Basic


namespace CategoryTheory.Distributors

def opObj (P : Dist A B) : Dist Bᵒᵖ Aᵒᵖ := (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _) ⋙ P

def op : (Dist A B) ⥤ Dist Bᵒᵖ Aᵒᵖ where
  obj := opObj
  map := whiskerLeft (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _)


end CategoryTheory.Distributors
