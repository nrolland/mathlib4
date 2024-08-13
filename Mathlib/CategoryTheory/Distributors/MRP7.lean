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


-----

-- works for set ...
def oneX : Discrete PUnit ⥤ Type := sorry
def oneL : Discrete PUnit ⥤ Type := sorry
noncomputable example := Functor.leftKanExtension oneL oneX

--
variable (C :  Cat)
def oneFunctorToSet : C ⥤ Type := sorry
def anotherFunctorToSet : C ⥤ Type := sorry

noncomputable example := Functor.leftKanExtension (oneFunctorToSet C) (anotherFunctorToSet C)
example := Limits.colimit (anotherFunctorToSet C)

-- presheaves
def onePsh : Discrete PUnit ⥤ C ⥤ Type := sorry
def anotherPsh : Discrete PUnit ⥤ C ⥤ Type := sorry

noncomputable example := Functor.leftKanExtension (onePsh C)  (anotherPsh C)
noncomputable example := Functor.leftKanExtension oneL  (anotherPsh C)
example := Limits.colimit (anotherPsh C)



-- Cat has limits, so does this work better ?
def typeCat : Cat := Cat.of Type
example : Cat := Cat.of (C ⥤ typeCat)
example := C ⟶ typeCat
--example : Cat := C ⟶ typeCat

def anotherPshCat : Cat.of (Discrete PUnit) ⟶ Cat.of (C ⥤ typeCat ):= sorry
example := Limits.colimit (anotherPshCat C)


-- il faudrait écrire CoLimits.lean dans /Cat pour montrer que Cat a les colimites ?
-- non cela ne repond pas a la question
-- il faudrait montrer que la categorie de foncteurs [C^op × A , Type] est cocomplete




end CategoryTheory
