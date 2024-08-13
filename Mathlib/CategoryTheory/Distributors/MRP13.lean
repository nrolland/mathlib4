import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements

universe u

namespace CategoryTheory

variable (B : Type (u) ) [Category.{u} B]

def proj : (Functor.hom B).Elements ⥤ Bᵒᵖ × B := CategoryOfElements.π (Functor.hom B)

def r : Bᵒᵖ × B ⥤ Type (u) := Functor.hom B

def a : Type (u):= (Functor.hom B).Elements
def b : Type (u) :=  Bᵒᵖ × B


def a' := Cat.of (Functor.hom B).Elements
def b' := Cat.of (Bᵒᵖ × B)


def proj_in_cat :  Cat.of (Functor.hom B).Elements ⟶ Cat.of (Bᵒᵖ × B) := proj B
-- failed to solve universe constraint
--   u+1 =?= max u ?u.298
-- while trying to unify
--   Type (u + 1) : Type (u + 2)
-- with
--   Type u : Type (u + 1)


end CategoryTheory
