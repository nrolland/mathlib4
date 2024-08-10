import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Bicategory.Extension
import Mathlib.CategoryTheory.PUnit

namespace CategoryTheory


universe v₁ v₂ v₃ u₁ u₂

variable (A B C D : Cat)


def  asd   := Functor.star C
def asda  : C ⟶ _  := asd
