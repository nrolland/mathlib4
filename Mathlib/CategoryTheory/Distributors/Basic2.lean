/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Types

open CategoryTheory

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
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

structure CoWedge : Type (max (max um u₂) vm) where
  pt : M
  leg (b:B) : F.obj (Opposite.op b,b) ⟶ pt
  cowedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
     (F.map (f.op, 𝟙 c) ≫ leg c : F.obj (Opposite.op c', c) ⟶  pt)  =
     (F.map ((𝟙 c').op, f) ≫ leg c'  : F.obj (Opposite.op c', c)  ⟶  pt) := by aesop_cat

structure CoWedgeMorphism (x y : CoWedge F) where
  Hom : x.pt ⟶ y.pt
  cowedgeCondition : ∀ (c : B), x.leg c ≫ Hom = y.leg c := by aesop_cat

attribute [simp] CoWedgeMorphism.cowedgeCondition

instance : Category (CoWedge F) where
  Hom := fun x y => CoWedgeMorphism _ x y
  id := fun x => {Hom := 𝟙 x.pt}
  comp := fun {X Y Z} f g => {
    Hom := f.Hom ≫ g.Hom
    cowedgeCondition := fun c => by rw [<- Category.assoc]; aesop_cat }

----



def total (F : B ⥤ Type u) : Type (max u₂ u) :=  Σb: B, F.obj b

def relation (F : B ⥤ Type u) (e : total F)  (e' : total F) : Prop :=
  match e, e' with
  | ⟨a,x⟩, ⟨b,y⟩ => ∃ (f : a ⟶ b), y = F.map f x


def myCoend (F : Bᵒᵖ × B ⥤ Type _) : CoWedge F  where
  pt := total F
  leg b x := ⟨b,x⟩
  cowedgeCondition b b' f  := by
    let one : F.obj (Opposite.op b', b) ⟶ total F := F.map (f.op, 𝟙 b) ≫ (fun x => Sigma.mk b x)
    let two : F.obj (Opposite.op b', b) ⟶ total F := F.map ((𝟙 b').op, f) ≫ (fun x => Sigma.mk b' x)
    funext
    -- because it's a quotient
    sorry


#min_imports
