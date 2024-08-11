import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.PUnit

import Mathlib.CategoryTheory.Functor.KanExtension.Basic


namespace CategoryTheory


def oneX : Discrete PUnit ⥤ Type := sorry

def oneL : Discrete PUnit ⥤ Type := sorry


noncomputable def kanExample := Functor.leftKanExtension oneL oneX
