import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Distributors.LimitGroupoid

open CategoryTheory
open CategoryOfElements
open Functor
open Opposite

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)
set_option linter.longLine false
infixr:90 " ⋗ " => fun f g ↦ Function.comp g f

@[ext]
structure Wedge : Type (max (max um u₂) vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj (op c,c)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (op c, c')) := by aesop_cat

@[ext]
structure WedgeMorphism  {F : (Bᵒᵖ×B) ⥤ M} (x y : Wedge F) where
  hom : x.pt ⟶ y.pt
  fac : ∀ (c : B), hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.fac

instance : Category (Wedge F) where
  Hom x y:=  WedgeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := {
    hom := f.hom ≫ g.hom
    fac := fun c => by
      simp_all only [Category.assoc, WedgeMorphism.fac]
    }


abbrev End :=  Σ w : Wedge F, Limits.IsTerminal w

def Limits.asEmptyConeMorphism {x y : C} (f : x ⟶ y) :
    Limits.ConeMorphism (Limits.asEmptyCone x) (Limits.asEmptyCone y) :=
    { hom := f }

instance endGroupoid : Groupoid (End F) where
  Hom x y:=  WedgeMorphism x.1 y.1
  id x := 𝟙 x.1
  comp {x y z} (f : x.1 ⟶ y.1) (g : y.1 ⟶ z.1) := (f ≫ g : WedgeMorphism x.1 z.1)
  inv {x y} _ : y.fst ⟶ x.fst  :=  (Limits.IsLimit.lift x.2 ( Limits.asEmptyCone y.1))
  inv_comp {x y} (f : x.fst ⟶ y.fst) :=
    let h :  Limits.asEmptyConeMorphism ((Limits.IsLimit.liftConeMorphism x.2 ( Limits.asEmptyCone y.1)).hom ≫ f) =  (Limits.asEmptyConeMorphism (𝟙 y.1)) := Limits.IsLimit.uniq_cone_morphism y.2
    congrArg Limits.ConeMorphism.hom h
  comp_inv {x y} (f : x.fst ⟶ y.fst)  :=
    let h : Limits.asEmptyConeMorphism (f ≫ (Limits.IsLimit.liftConeMorphism x.2 ( Limits.asEmptyCone y.1)).hom) =  (Limits.asEmptyConeMorphism (𝟙 x.1)) := Limits.IsLimit.uniq_cone_morphism x.2
    congrArg Limits.ConeMorphism.hom h

instance endGroupoid2 : Groupoid (End F) := terminalGroupoid
