import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.EqToHomD
import Mathlib.CategoryTheory.Distributors.TerminalD

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₂ } [Category.{v₂} C]

variable (F G : J ⥤ B)

abbrev Limit  :=  Σ x : Cone F, IsLimit x
instance limitGroupoid : Groupoid (Limit F) where
  Hom x y  :=  ConeMorphism x.1 y.1
  id x := 𝟙 x.1
  comp f g := Cone.category.comp f g
  inv {x y} _  := IsLimit.liftConeMorphism x.2 y.1
  inv_comp {_ y} _ := IsLimit.uniq_cone_morphism y.2
  comp_inv {x _} _ := IsLimit.uniq_cone_morphism x.2

def limitConnected (x y : Limit F) : x ⟶ y := IsLimit.liftConeMorphism y.2 x.1

def limitFctr : (J ⥤ B) ⥤ Cat where -- a generaliser a Cat / Cat
  obj f := Cat.of (Limit f )
  map {f g } α := sorry
  map_id f := sorry
  map_comp := sorry

--facile
def isoFunctorIsoLimit {F G : J ⥤ B} (i: F ≅ G)  : Cat.of (Limit F) ≅ Cat.of (Limit G) :=
  Functor.mapIso limitFctr i


-- pas facile
def isoFunctorIsoLimit2 (i : IsoOfCategory (J ⥤ B) (J ⥤ C)) (F : J ⥤ B ) :
    Cat.of (Limit F) ≅ Cat.of (Limit (G)) :=
    -- categorie des cones iso
    -- terminal iso
    sorry

-- #min_imports


-- Pour notre affaire :

-- B(F-,G=) : bop * b -> set
-- [Bop,Set](B( , F-), B( , G=)) : bop * b -> set
-- iso

-- categorie de wedge pour  B(F-,G=)
-- categorie de wedge pour l'autre
-- iso

-- terminal pour l'un
-- terminal pour l'autre
-- iso


-- pour end ou pour limit, iso terminal est clef
