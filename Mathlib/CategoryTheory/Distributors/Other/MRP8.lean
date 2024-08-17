import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types

namespace CategoryTheory
open Limits

universe u
variable (A : Type) [Category A]
variable (P : A ⥤ Type u)

-- Question 1 : I imagine Type has the colimits somewhere, but where ?
def sad : HasColimit P := inferInstance  -- failed to synthesize  Limits.HasColimit P


variable (C :  Cat)
variable (QfromCat : C ⥤ Type u)

-- Question 2 : Why can I take limits now  ?
def happy := colimit QfromCat

-- Question 2' : Why can I take limits when i can't get HasLimit ?
def happy_but_sad! : HasColimit QfromCat := inferInstance -- failed to synthesize Limits.HasColimit QfromCat

variable (declaration_of_something_else_in_cat : C ⟶ Cat.of Type)

-- Question 3 : Why can't I now have colimits ?
def happy_but_notanymore := colimit QfromCat  --failed to synthesize Limits.HasColimit Q


end CategoryTheory
