import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types

universe v₂ u₂

namespace CategoryTheory

variable {B : Type u₂ } [Category.{u₂+1} B]

open Limits

def extend (F : Bᵒᵖ × B ⥤ Type (u₂+1)) : (Functor.hom B).Elements ⥤ Type (u₂+1)  :=
  CategoryOfElements.π (Functor.hom B) ⋙ F


--failed to compile definition, consider marking it as 'noncomputable' because it depends on 'CategoryTheory.Limits.colimit.isColimit', and it does not have executable code
def coendl : (Bᵒᵖ × B ⥤ Type (u₂+1)) ⥤ (Type (u₂+1)) where
  obj (f : Bᵒᵖ × B ⥤ Type (u₂ + 1)) := Limits.colimit (extend f)
  map {f g} (n : f ⟶ g) :=
      (colimit.isColimit (extend f)).desc
        ((Cocones.precompose (whiskerLeft (CategoryOfElements.π (Functor.hom B)) n)).obj
         (colimit.cocone (extend g)))
  map_id := sorry
  map_comp := sorry

end CategoryTheory
