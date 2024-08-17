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


-- works for set ...
def oneX : Discrete PUnit ⥤ Type := sorry

def oneL : Discrete PUnit ⥤ Type := sorry


noncomputable def kanExample := Functor.leftKanExtension oneL oneX



--

variable (C :  Cat)

def oneFunctorToSet : C ⥤ Type := sorry

def anotherFunctorToSet : C ⥤ Type := sorry

noncomputable def kanExample' := Functor.leftKanExtension (oneFunctorToSet C)
  (anotherFunctorToSet C)


-- presheaves


def onePsh : Discrete PUnit ⥤ C ⥤ Type := sorry

def anotherPsh : Discrete PUnit ⥤ C ⥤ Type := sorry


noncomputable def kanExample'' := Functor.leftKanExtension (onePsh C)
  (anotherPsh C)


noncomputable def kanExample''' := Functor.leftKanExtension oneL  (anotherPsh C)




end CategoryTheory
