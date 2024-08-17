import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory
open Limits

universe v₁ v₂ vm u₁ u₂ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]


structure IsTerminalSimple (t : B) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : B, s ⟶ t
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : B) (m : s ⟶ t), m = lift s := by
    aesop_cat

structure IsLimit (t : Cone (Functor.empty.{0} B)) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone (Functor.empty.{0} B), s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone (Functor.empty.{0} B)) (j : Discrete.{0} PEmpty), lift s ≫ t.π.app j = s.π.app j := by aesop_cat
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : Cone (Functor.empty.{0} B)) (m : s.pt ⟶ t.pt) (_ : ∀ j : Discrete.{0} PEmpty, m ≫ t.π.app j = s.π.app j), m = lift s := by
    aesop_cat


def toCone (b : B ) : Cone (Functor.empty.{0} B) := sorry


def terminalWedgeToLimitOfEmptyDiag {t:B} (w : IsTerminalSimple t) :  LimitCone ( Functor.empty.{0} B) := sorry


variable (F : (Bᵒᵖ×B) ⥤ M)

structure Wedge : Type (max (max um u₂) vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj (Opposite.op c,c)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (Opposite.op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (Opposite.op c, c')) := by aesop_cat

structure WedgeMorphism (x y : Wedge F) where
  Hom : x.pt ⟶ y.pt
  wedgeCondition : ∀ (c : B),
    Hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.wedgeCondition

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism _ x y
  id := fun x => {  Hom := 𝟙 x.pt }
  comp := fun f g =>  { Hom := f.Hom ≫ g.Hom}


-- Definition of end via wedges
noncomputable def end_summit [HasTerminal (Wedge F)] := terminal (Wedge F)

def endCone [Limits.HasLimit ((CategoryOfElements.π (Functor.hom B)) ⋙ F)] : Type _ :=
  Limits.LimitCone ((CategoryOfElements.π (Functor.hom B)) ⋙ F)


-- missing : a wedge for F is a cone for F . pi
