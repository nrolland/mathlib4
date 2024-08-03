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
variable (F : C ⥤ D)

def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True
def isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

lemma transport (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
   obtain ⟨f,_⟩ := h
   exact ⟨F.map f, trivial⟩

def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected

-- Transport d'un x vers sa composante
def toCC (x : C) : Quotient (@catisSetoid C) := Quotient.mk (@catisSetoid C) x

-- ensemble des composantes d'une categorie
-- def ccSet (C : Cat) := { toCC x | x : C }

abbrev ccSet  (C : Cat) := Quotient (@catisSetoid C)
-- def toCC2 (x: C) : ccSet C := ⟨toCC x, by use x⟩


lemma transportExt  (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w
  case trans f g => exact EqvGen.trans _ _ _ f g


def quot_closure{α : Type u} (r : α → α → Prop) a b := Quot.mk r a = Quot.mk r  b
def isQuotClosed  : C → C → Prop   := quot_closure isConnected
lemma functorialityQuotClosed (a b : C) : isQuotClosed a b → isQuotClosed (F.obj a) (F.obj b) :=
   Quot.EqvGen_sound ∘ transportExt F ∘ Quot.exact isConnected


lemma transportExtQuot (a b : C) : isConnectedByZigZag a b → toCC (F.obj a) = toCC (F.obj b) :=
    Quot.sound ∘ transportExt F

-- -- induction is not case analysis
-- lemma functoriality3 (F : C ⥤ D) (a b : C) (h: isConnectedByZigZag a b) : toCC (F.obj a) = toCC (F.obj b) := by
--   induction h
--   case rel a b h => exact (transport F h) |> EqvGen.rel _ _ |> Quot.sound
--   case refl x => exact EqvGen.refl _  |> Quot.sound
--   case symm w  => exact Quotient.exact w /- not case -/|> EqvGen.symm _ _ |> Quot.sound
--   case trans _  _ _ f g => sorry


def fmap {X Y : Cat} (F : X ⟶ Y) : (ccSet X) → (ccSet Y) := fun x ↦
    Quotient.lift (s:= @catisSetoid X)
                  (toCC ∘ F.obj  : X → ccSet Y)
                  (fun _ _ => Quot.sound ∘ transportExt F )
                  x

def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ccSet C -- maps a category to its set of CC
  map {X Y} F := fmap F
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
