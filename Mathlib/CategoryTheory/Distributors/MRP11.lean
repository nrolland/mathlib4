/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
namespace CategoryTheory

universe v u
variable (A : Type u) [Category A]
variable (C :  Cat.{u,u+1})
variable [Category C]
variable (P : A ⥤ Type u) -- (Q : C ⥤ Type u)


--abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C
--abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C

def catInst : LargeCategory.{u} (Type u) := inferInstance

def catInsts  : LargeCategory.{u} (Type u : Type (u+1)) := inferInstance
def catInstsas : Category.{u,u+1} (Type u : Type (u+1)) := inferInstance
def catIns : Category.{u} (Type u : Type (u+1)) := inferInstance
def catInsasd : Cat.{u,u+1} := Cat.of (Type u)

def as.{u'} : Cat.{u',u'+1}  := Cat.of.{u',(u'+1)} (Type u')

def R : Cat.{u,u+1}  := as.{u}


variable (asR : C ⟶  R)

variable (C :  Cat)
variable (S : C ⟶ Cat.of (Type u))
variable (C :  Cat.{u})
variable (S : C ⟶ Cat.of (Type u))
variable (C :  Cat.{u,u+1})
variable (S : C ⟶ Cat.of (Type u))


def happyasd := Limits.colimit P

-- /-- The obvious projection functor from structured arrows. -/
-- def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
--   Comma.snd _ _

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable (A : Type u₁ ) [Category.{v₁} A]
variable (B : Type u₂ ) [Category.{u₂+1} B]
variable (C : Type u₃ ) [Category.{v₃} C]
variable (D : Type u₄ ) [Category.{v₄} D]

abbrev Dist := Bᵒᵖ × A ⥤ Type u

open MonoidalCategory
open CategoryTheory.Bifunctor

-- noncomputable def composition (P : Dist A B) (Q: Dist B C) :  Dist A C  :=
--   let PtimesQ : ((↑B)ᵒᵖ × ↑B) × ((↑C)ᵒᵖ × ↑A) ⥤ Type :=
--     prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
--     Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ prod.inverseAssociator _ _ _  ⋙
--     Functor.prod (𝟭 _) (Prod.swap _ _) ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type
--   -- noncomputable example := Functor.leftKanExtension oneL oneX
--   let mynicefunctor : (Functor.hom B).Elements ⥤ (Cᵒᵖ × A ⥤ Type) := CategoryOfElements.π (CategoryTheory.Functor.hom B) ⋙ curryObj PtimesQ

--   let sad := Limits.colimit mynicefunctor
--   let sad := Functor.pointwiseLeftKanExtension (Functor.star ((CategoryTheory.Functor.hom B)).Elements) mynicefunctor
--   let sad := sad.obj (⟨⟨⟩⟩)

--   sad

open Limits

def one  : (Functor.hom B).Elements ⥤ Bᵒᵖ × B := CategoryOfElements.π (Functor.hom B)
def two  : Bᵒᵖ × B ⥤ Type (u₂ + 1)  := Functor.hom B
def  onetwo  : (Functor.hom B).Elements ⥤ Type (u₂ + 1) := one B ⋙ two B

#synth HasColimit (onetwo B)

def simpler   :=
  let one  : (Functor.hom B).Elements ⥤ Bᵒᵖ × B := CategoryOfElements.π (Functor.hom B)
  let two  : Bᵒᵖ × B ⥤ Type (u₂ + 1) := Functor.hom B
  let onetwo  : (Functor.hom B).Elements ⥤ Type (u₂ + 1) := one ⋙ two

  let sad1 := Limits.colimit onetwo

  let dom  : Type (u₂ + 1) := ((Functor.hom B)).Elements
  let bang  : dom ⥤ Discrete PUnit.{u + 1} := Functor.star dom
--  let bang  :  CategoryTheory.Functor.star.{w, v, u} (C : Type u) [Category.{v, u} C] : C ⥤ Discrete PUnit.{w + 1} := ((Functor.hom B)).Elements
  let sad := Functor.pointwiseLeftKanExtension bang onetwo
  -- let sad := sad.obj (⟨⟨⟩⟩)

  sad1

end CategoryTheory
