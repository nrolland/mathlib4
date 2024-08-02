/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions related to Cat, the category of categories

The embedding `Type ⥤ Cat` has a right adjoint `Cat.objects` mapping
each category to its set of objects.


## TODO
The embedding `Type ⥤ Cat` has a left adjoint `Cat.connectedComponents` mapping
each category to its set of connected components.

-/


universe v u

namespace CategoryTheory

section AdjDiscObj

variable (X : Type u)
variable (C : Cat)

private def lxyToxry : (typeToCat.obj X ⟶ C) → (X ⟶ Cat.objects.obj C) := fun f x ↦ f.obj ⟨x⟩
private def xryTolxy : (X ⟶ Cat.objects.obj C) → (typeToCat.obj X ⟶ C) := fun f ↦ Discrete.functor f

private lemma linverse : Function.LeftInverse (xryTolxy X C) (lxyToxry X C) :=
  fun (fctr : typeToCat.obj X ⥤ C) ↦ by
  fapply Functor.hext
  · intro x; rfl
  · intro ⟨x⟩ ⟨y⟩ f
    simp
    obtain rfl := (Discrete.eq_of_hom f : x = y)
    calc
      (xryTolxy X C (lxyToxry X C fctr)).map f = 𝟙 (fctr.obj { as := x }) :=
        Discrete.functor_map_id (xryTolxy X C (lxyToxry X C fctr)) f
      _                                        = fctr.map f := (Discrete.functor_map_id fctr f).symm

private lemma rightinverse : Function.RightInverse (xryTolxy X C) (lxyToxry X C) := fun _ ↦ by
  fapply funext
  intro x
  rfl

private def homEquiv : ∀ X C, (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) := fun X C ↦ by
    apply Equiv.mk
      (lxyToxry X C)
      (xryTolxy X C)
      (linverse X C)
      (rightinverse X C)

private def counit_app : ∀ C,  (Cat.objects ⋙ typeToCat).obj C ⥤ C := fun C =>
    { obj := Discrete.as
      map := eqToHom ∘ Discrete.eq_of_hom }


/-- typeToCat : Type ⥤ Cat is left adjoint to Cat.objects : Cat ⥤ Type
-/
def adjTypeToCatCatobjects : typeToCat ⊣ Cat.objects where
  homEquiv  := homEquiv
  unit : 𝟭 (Type u) ⟶ typeToCat ⋙ Cat.objects := { app:= fun X  ↦ Discrete.mk }
  counit : Cat.objects ⋙ typeToCat ⟶ 𝟭 Cat :=
  {
    app := counit_app
    naturality := by intro C D (f : C ⥤ D)
                     fapply Functor.hext
                     · intro c
                       rfl
                     · intro ⟨_⟩ ⟨_⟩ f
                       obtain rfl := Discrete.eq_of_hom f
                       aesop_cat
  }

end AdjDiscObj


section AdjCC

variable (X : Type u)
variable {C D : Cat}
variable {α : Type u}
variable {a b : C}

def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True
def refl_trans_symm_closure (r : α → α → Prop) a b := Quot.mk r a = Quot.mk r  b

def isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected

def toCC x := Quotient.mk (@catisSetoid C) x
def cc (C : Cat) := { toCC x | x : C }


lemma functoriality (h : isConnected a b ) (F : C ⥤ D) : isConnected (F.obj a) (F.obj b) := sorry



def asas := (· + 1)

def amap  (F : C ⥤ D)  : C → cc D := fun x => ⟨toCC (F.obj x), by use (F.obj x)⟩

def amap'  (F : C ⥤ D) := Quotient.lift (s:= @catisSetoid C) (amap F)

def p (F : ↑C ⥤ ↑D) : (∀ (a b : ↑C), isConnectedByZigZag a b → amap F a = amap F b) := fun a b h ↦
    have : Quot.mk isConnected a = Quot.mk isConnected  b := h
    by
        have : True := sorry
        sorry

#check amap'

-- CategoryTheory.amap'.{u_1, u_2, u_3, u_4} {C : Cat} {D : Cat} (F : ↑C ⥤ ↑D) :
--   (∀ (a b : ↑C), a ≈ b → amap F a = amap F b) → Quotient catisSetoid → ↑(cc D)

def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := cc C -- maps a category to its set of CC
  map {X Y} F := fun ⟨x,_⟩ ↦  sorry

---/lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) : ((a b : α) → a ≈ b → f a = f b) → Quotient s → β



def lxyToxry' : (connectedComponents.obj C ⟶ X) → (C ⟶ typeToCat.obj X) := sorry
def xryTolxy' :  (C ⟶ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := sorry


def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := sorry
  unit  := sorry
  counit := sorry


end AdjCC


end CategoryTheory
