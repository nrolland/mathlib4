import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso

open CategoryTheory
open Limits

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

def limitFctr : (J ⥤ B ) ⥤ Cat where
  obj f := Cat.of (Limit f )
  map {f g } α := sorry
  map_id f := sorry
  map_comp := sorry

def isoDiagIsoLimit {F G : J ⥤ B} (i: F ≅ G)  : Cat.of (Limit F) ≅ Cat.of (Limit G) :=
  Functor.mapIso limitFctr i


abbrev Terminal (B : Type u₂ ) [Category.{v₂} B] :=  Σ x : B, IsTerminal x

instance terminalGroupoid : Groupoid (Terminal B) where
  Hom x y  :=  x.1 ⟶ y.1
  id x := 𝟙 x.1
  comp {x y z} f g :=  f ≫ g
  inv {x y} _  :=  IsTerminal.from x.2 y.1
  inv_comp {_ y} _ := IsTerminal.hom_ext y.2 _ _
  comp_inv {x _} _ := IsTerminal.hom_ext x.2 _ _


def terminalConnected (x y : Terminal B) : x ⟶ y := Limits.IsTerminal.from y.2 x.1

def isoCatIsoTerminal  (i: B ≅ C)  : Terminal B ≅ Terminal C where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry



-- def uniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s ≅ t
-- theorem hom_isIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (f : s ⟶ t) : IsIso f
-- def equivIsoLimit {r t : Cone F} (i : r ≅ t) : IsLimit r ≃ IsLimit t
-- def ofIsoLimit {r t : Cone F} (P : IsLimit r) (i : r ≅ t) : IsLimit t
--uliftFunctor
