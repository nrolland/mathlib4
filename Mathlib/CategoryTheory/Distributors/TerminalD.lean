import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.EqToHomD
import Mathlib.CategoryTheory.Distributors.WhiskeringD

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um w
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]

def asEmptyConeMorphism {x y : C} (f : x ⟶ y) :
    Limits.ConeMorphism (Limits.asEmptyCone x) (Limits.asEmptyCone y) :=
    { hom := f }

abbrev Terminal (B : Type u₂ ) [Category.{v₂} B] :=  Σ x : B, IsTerminal x
instance terminalGroupoid : Groupoid (Terminal B) where
  Hom x y  :=  x.1 ⟶ y.1
  id x := 𝟙 x.1
  comp {x y z} f g :=  f ≫ g
  inv {x y} _  :=  IsTerminal.from x.2 y.1
  inv_comp {_ y} _ := IsTerminal.hom_ext y.2 _ _
  comp_inv {x _} _ := IsTerminal.hom_ext x.2 _ _
def terminalConnected (x y : Terminal B) : x ⟶ y := Limits.IsTerminal.from y.2 x.1
-- def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T'


theorem uniq_morphism_to_terminal {s t : B} (h : IsTerminal t) {f f' : s ⟶ t} : f = f' :=
  congrArg ConeMorphism.hom (uniq_cone_morphism h : asEmptyConeMorphism f = asEmptyConeMorphism f')

def qeqe  (i: IsoOfCategory B C) (x : B ) : (IsTerminal x) ≃ (IsTerminal (i.hom.obj x)) := sorry

def emptyConeExt {a b : Cone (Functor.empty C)} (h : a.pt = b.pt) : a ≅ b :=
  Cones.ext (eqToIso h) (fun a => a.as.elim)
