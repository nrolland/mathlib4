import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory
open Limits

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)

structure CoWedge : Type (max (max um u₂) vm) where
  pt : M
  leg (b:B) : F.obj (Opposite.op b,b) ⟶ pt
  cowedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
     (F.map (f.op, 𝟙 c) ≫ leg c : F.obj (Opposite.op c', c) ⟶  pt)  =
     (F.map ((𝟙 c').op, f) ≫ leg c'  : F.obj (Opposite.op c', c)  ⟶  pt) := by aesop_cat

structure CoWedgeMorphism (x y : CoWedge F) where
  Hom : x.pt ⟶ y.pt
  fac : ∀ (c : B), x.leg c ≫ Hom = y.leg c := by aesop_cat

attribute [simp] CoWedgeMorphism.fac

instance : Category (CoWedge F) where
  Hom := fun x y => CoWedgeMorphism _ x y
  id := fun x => {Hom := 𝟙 x.pt}
  comp := fun {X Y Z} f g => {
    Hom := f.Hom ≫ g.Hom
    fac := fun c => by rw [<- Category.assoc]; aesop_cat }

-- missing 0 IsCoend

noncomputable def coend_nadir [HasInitial (CoWedge F)] := initial (CoWedge F)


-- missing : a cowedge for F is a cocone for F . pi

-- missing : a coend is a colimit for F . pi
