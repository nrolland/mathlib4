/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types

universe v   u

namespace CategoryTheory
set_option linter.longLine false

open Limits
open Bicategory



section easy

variable {B : Cat.{u,u+1}}

-- I need extend to go to  Type (u+1) because I need HasColimits
def extend (F : Bᵒᵖ × B ⥤ Type (u+1)) : (Functor.hom B).Elements ⥤ Type (u+1)  := CategoryOfElements.π (Functor.hom B) ⋙ F
def colimd (EF : (Functor.hom B).Elements ⥤ Type (u+1)): Type (u+1) := Limits.colimit EF -- I go to u+1, so I HasColimits

-- let's write a functor
def coendFunctor : (Bᵒᵖ × B ⥤ Type (u+1)) ⥤ Type (u+1) where
  obj (f : Bᵒᵖ × B ⥤ Type (u + 1)) := colimd (extend f)
  map {f g} (n : f ⟶ g) := by
    -- I get a natural transformation f ⟶ g, which i turn into a natural transformation (extend f) ⟶ (extend g)
    let n2 : (extend f) ⟶ (extend g) := sorry
    -- let's do it with the API of Cat as a 2-category, that's what it's made for !
    sorry
  map_id := sorry
  map_comp := sorry
end easy


section letsBeSmarter

variable {B : Cat.{u,u+1}}

-- Cat is a 2-category. So I can use
-- Bicategory.precomposing  (a b c : Cat) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c)

-- error
def precompFail := Bicategory.precomposing (Cat.of (Functor.hom B).Elements) (Cat.of (Bᵒᵖ × B)) (Cat.of (Type (u+1)))
-- application type mismatch
--   @Cat.of (Type (u + 1))
-- argument
--   Type (u + 1)
-- has type
--   Type (u + 2) : Type (u + 3)
-- but is expected to have type
--   Type (u + 1) : Type (u + 2)

-- lots of head scraching...

end letsBeSmarter -- dont be smart. don't abstract.


section oneLastTry

-- this works
variable {B : Cat.{u+1,u+2}}

-- we have precomp functor
def precomp :
  (Cat.of (Functor.hom ↑B).Elements ⟶ Cat.of ((↑B)ᵒᵖ × ↑B)) ⥤
    (Cat.of ((↑B)ᵒᵖ × ↑B) ⟶ Cat.of (Type (u + 1))) ⥤ (Cat.of (Functor.hom ↑B).Elements ⟶ Cat.of (Type (u + 1)))
    := Bicategory.precomposing (Cat.of (Functor.hom B).Elements) (Cat.of (Bᵒᵖ × B)) (Cat.of (Type (u+1)))

-- but now we can't take limits
def colimdFail (EF : (Functor.hom B).Elements ⥤ Type (u+1)): Type (u+1) := Limits.colimit EF -- No HasColimits

-- unless we go to u+2
def colimd2ok (EF : (Functor.hom B).Elements ⥤ Type (u+2)): Type (u+2) := Limits.colimit EF -- I HasColimits

-- but the of course we go back to square one !

end oneLastTry



end CategoryTheory
