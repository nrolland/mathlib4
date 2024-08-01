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

def _lxyToxry : (typeToCat.obj X ⟶ C) → (X ⟶ Cat.objects.obj C) := fun f x ↦ f.obj ⟨x⟩
def _xryTolxy :  (X ⟶ Cat.objects.obj C) → (typeToCat.obj X ⟶ C) := fun f ↦ Discrete.functor f

lemma _linverse : Function.LeftInverse (_xryTolxy X C) (_lxyToxry X C) :=
  fun (fctr : typeToCat.obj X ⥤ C) ↦ by
  fapply Functor.hext
  · intro x; rfl
  · intro ⟨x⟩ ⟨y⟩ f
    simp
    obtain rfl := (Discrete.eq_of_hom f : x = y)
    calc
      (_xryTolxy X C (_lxyToxry X C fctr)).map f = 𝟙 (fctr.obj { as := x }) :=
        Discrete.functor_map_id (_xryTolxy X C (_lxyToxry X C fctr)) f
      _                                        = fctr.map f := (Discrete.functor_map_id fctr f).symm

lemma _rightinverse : Function.RightInverse (_xryTolxy X C) (_lxyToxry X C) := fun (f : X → C ) ↦ by
  fapply funext
  intro x
  rfl

def _homEquiv : ∀ X C, (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) := fun X C ↦ by
    apply Equiv.mk
      (_lxyToxry X C)
      (_xryTolxy X C)
      (_linverse X C)
      (_rightinverse X C)

def _counit_app : ∀ C,  (Cat.objects ⋙ typeToCat).obj C ⥤ C := fun C =>
    { obj := Discrete.as
      map := eqToHom ∘ Discrete.eq_of_hom }


/-- typeToCat : Type ⥤ Cat is left adjoint to Cat.objects : Cat ⥤ Type
-/
def adjTypeToCatCatobjects : typeToCat ⊣ Cat.objects where
  homEquiv  := _homEquiv
  unit : 𝟭 (Type u) ⟶ typeToCat ⋙ Cat.objects := { app:= fun X  ↦ Discrete.mk }
  counit : Cat.objects ⋙ typeToCat ⟶ 𝟭 Cat :=
  {
    app := _counit_app
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
variable {C : Cat}
variable {α : Type u}

-- a symetriser
def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True
def refl_trans_symm_closure (r : α → α → Prop) a b := Quot.mk r a = Quot.mk r  b

-- class Setoid (α : Sort u) where
--   r : α → α → Prop
--   iseqv : Equivalence r

def catisSetoid : Setoid C where
  r := refl_trans_symm_closure isConnected
  iseqv := {  refl  := fun _ => rfl -- ∀ x, r x x
              symm  := Eq.symm --  ∀ {x y}, r x y → r y x
              trans := Eq.trans -- ∀ {x y z}, r x y → r y z → r x z
              }

#check @catisSetoid C



def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := { Quotient.mk (@catisSetoid C) x | x : C }
  map F := sorry

def _lxyToxry' : (connectedComponents.obj C ⟶ X) → (C ⟶ typeToCat.obj X) := sorry
def _xryTolxy' :  (C ⟶ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := sorry


def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := sorry
  unit  := sorry
  counit := sorry


end AdjCC

end CategoryTheory
