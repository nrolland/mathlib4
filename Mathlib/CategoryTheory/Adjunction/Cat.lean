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
def isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

-- def quot_closure{α : Type u} (r : α → α → Prop) a b := Quot.mk r a = Quot.mk r  b
-- def isQuotClosed  : C → C → Prop   := quot_closure isConnected

def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected

def toCC x := Quotient.mk (@catisSetoid C) x
def cc (C : Cat) := { toCC x | x : C }


lemma functoriality (F : C ⥤ D)
        (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel _ _ h => obtain ⟨f,_⟩ := h
                    exact (EqvGen.rel _ _ ⟨F.map f, trivial⟩)
  case refl x => exact EqvGen.refl (F.obj x)
  case symm _ _ w => exact EqvGen.symm _ _ w
  case trans _  _ _ f g => exact EqvGen.trans _ _ _ f g



lemma functoriality2 (F : C ⥤ D) (a b : C) : isQuotClosed a b → isQuotClosed (F.obj a) (F.obj b) :=
   Quot.EqvGen_sound ∘ functoriality F ∘ Quot.exact isConnected

def amap  (F : C ⥤ D)  : C → cc D := fun x => ⟨toCC (F.obj x), by use (F.obj x)⟩

lemma functoriality3 (F : C ⥤ D) (a b : C) (h: isConnectedByZigZag a b) : amap F a = amap F b := by
  -- egalite sur existentiel... TBD
  induction h
  sorry
  sorry
  sorry
  sorry


def amap'  (F : C ⥤ D) :  Quotient (@catisSetoid C) → (cc D) :=
    Quotient.lift (s:= @catisSetoid C)
                  (amap F : C → cc D)
                  (sorry :  ∀ (a b : C), isConnectedByZigZag a b → amap F a = amap F b /- egalite sur existentiel -/)

def fmap {X Y : Cat} (F : X ⟶ Y) : (cc X) → (cc Y) := fun ⟨x,_⟩ ↦ amap' F x

#check amap'
-- CategoryTheory.amap'.{u_1, u_2, u_3, u_4} {C : Cat} {D : Cat} (F : ↑C ⥤ ↑D) :
--   (∀ (a b : ↑C), a ≈ b → amap F a = amap F b) → Quotient catisSetoid → ↑(cc D)

def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := cc C -- maps a category to its set of CC
  map {X Y} F := fun ⟨x,_⟩ ↦   amap' F x
  map_id := sorry
  map_comp := sorry



def lxyToxry' : (connectedComponents.obj C ⟶ X) → (C ⟶ typeToCat.obj X) := sorry
def xryTolxy' :  (C ⟶ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := sorry


def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := sorry
  unit  := sorry
  counit := sorry


end AdjCC


end CategoryTheory
