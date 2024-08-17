import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types

universe u

namespace CategoryTheory
variable {B : Cat.{u,u+1}}

-- I initially wanted to precompose functors by a specific functor
def extend (F : Bᵒᵖ × B ⥤ Type (u+1)) : (Functor.hom B).Elements ⥤ Type (u+1)  :=
  CategoryOfElements.π (Functor.hom B) ⋙ F

-- I need that recomposition to go to Type (u+1) because I need HasColimits
def colimd (EF : (Functor.hom B).Elements ⥤ Type (u+1)): Type (u+1) := Limits.colimit EF


def t := CategoryTheory.whiskerLeft


-- let's use Bicategory.precomposing, that's exactly what's needed
-- def precompFunctorFail
--     : (Cat.of (Functor.hom B).Elements ⟶ Cat.of (Bᵒᵖ × B)) ⥤
--         (Cat.of (Bᵒᵖ × B) ⟶ Cat.of (Type (u+1))) ⥤ (Cat.of (Functor.hom ↑B).Elements ⟶  Cat.of (Type (u+1)))
--     := Bicategory.precomposing (Cat.of (Functor.hom B).Elements) (Cat.of (Bᵒᵖ × B)) (Cat.of (Type (u+1)))
--       (CategoryOfElements.π (Functor.hom B))

noncomputable def coendl : (Bᵒᵖ × B ⥤ Type (u+1)) ⥤ (Type (u+1)) where
  obj (f : (↑B)ᵒᵖ × ↑B ⥤ Type (u₂ + 1)) := Limits.colimit (extend f)
  map {f g} (n : f ⟶ g) := by
    let n2 : NatTrans (extend f) (extend g) := whiskerLeft (CategoryOfElements.π (Functor.hom B)) n
    let m : (colimit.cocone (extend f)).pt → (colimit.cocone (extend g)).pt :=
      (colimit.isColimit (extend f)).desc ( (Cocones.precompose n2).obj (colimit.cocone (extend g)))
    simp
    exact m
  map_id := sorry
  map_comp := sorry





-- If that worked I could then use
def extendFunctor := precompFunctorFail.obj (CategoryOfElements.π (Functor.hom B))
def extend' := extendFunctor.obj

end CategoryTheory
