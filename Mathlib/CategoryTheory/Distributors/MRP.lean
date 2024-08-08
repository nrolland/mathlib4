import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.ChosenFiniteProducts

universe v u




namespace CategoryTheory



section TypeIsMonoidal



end  TypeIsMonoidal


noncomputable instance : MonoidalCategory Type := monoidalOfHasFiniteProducts Type

noncomputable def cart  : Type × Type ⥤ Type :=  MonoidalCategory.tensor Type

def x : Limits.HasTerminal Type :=  by infer_instance

#check  @monoidalOfChosenFiniteProducts


def asdsa : ChosenFiniteProducts Type := by infer_instance
def the_product :=  @monoidalOfChosenFiniteProducts Type sorry sorry sorry

def toto := the_product




end CategoryTheory
