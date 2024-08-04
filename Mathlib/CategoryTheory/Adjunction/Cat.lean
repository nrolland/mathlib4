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

/-! # Relation induced by a category

A category induces a relation on its objects
Two objects are connected if there is an arrow between them.
This relation is not an equivalence, as only reflexivity holds in general.

`{a:C}{b:C} (f : a ⟶ b) : isConnected a b := ⟨f, trivial⟩`
-/
def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True

/--
The relation is transported by functors
-/
lemma transport (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
   obtain ⟨f,_⟩ := h
   exact ⟨F.map f, trivial⟩


/-! ## Relation induced by a category

To make this relation an equivalence, one needs to take the equivalence closure
Two objects are connected if there is a zigzag of arrows between them.

-/
abbrev isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

private def rel {a:C}{b:C} (f : a ⟶ b) : isConnectedByZigZag a b := EqvGen.rel _ _ (⟨f, trivial⟩)


lemma transportExt  (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w
  case trans f g => exact EqvGen.trans _ _ _ f g

-- Other formulation
-- def isConnectedByQuotEq (a b : C) := Quot.mk isConnected a = Quot.mk isConnected  b
-- lemma functorialityQuotClosed : isConnectedByQuotEq a b →
--                                 isConnectedByQuotEq (F.obj a) (F.obj b) :=
--    Quot.EqvGen_sound ∘ transportExt F ∘ Quot.exact isConnected

--- Quotient based computation
def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected

-- Transport d'un x vers sa composante
def toCC (x : C) : Quotient (@catisSetoid C) := Quotient.mk (@catisSetoid C) x

-- Ensemble des composantes d'une categorie
abbrev ccSet  (C : Cat) := Quotient (@catisSetoid C)

lemma transportExtQuot (a b : C) : isConnectedByZigZag a b → toCC (F.obj a) = toCC (F.obj b) :=
    Quot.sound ∘ transportExt F

private def fmap {X Y : Cat} (F : X ⟶ Y) : (ccSet X) → (ccSet Y) :=
    Quotient.lift (s:= @catisSetoid X)
                  (toCC ∘ F.obj  : X → ccSet Y)
                  (fun _ _ => Quot.sound ∘ transportExt F )

private abbrev liftedMk (s : Setoid α)  := Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)

private def quotDecomp {s : Setoid α}  : ∀ xt : Quotient s, (∃ x, ⟦x⟧ = xt) :=
  Quotient.ind (motive:= (∃ x, Quotient.mk s x = ·)) (by simp; exact ⟨·, s.refl _⟩)

/- The functor for connected components -/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ccSet C -- maps a category to its set of CC
  map F := fmap F  -- transport a functor to a function beetwen CC
  map_id X := by calc
      fmap (𝟙 X) =  liftedMk (@catisSetoid X) := (rfl : fmap (𝟙 X) = liftedMk (@catisSetoid X))
      _                       = fun x => x    := by funext xt; obtain ⟨x,h⟩ := quotDecomp xt
                                                    simp [h.symm]
      _                       = 𝟙 (ccSet X)   := by rfl
  map_comp f g := by simp; funext xt; obtain ⟨_,h⟩ := quotDecomp xt;
                     simp [h.symm];rfl

#check congr

def laxToarx : (connectedComponents.obj C ⟶ X) → (C ⟶ typeToCat.obj X) := fun fct =>
  { obj := fun x => x |> Quotient.mk (@catisSetoid C) |> fct |> Discrete.mk
    map := fun {a b} f => by  simp
                              let as := toCC a
                              let bs := toCC b
                              have h : as = bs := Quot.sound (rel f)
                              have h': Discrete.mk ⟦a⟧ = Discrete.mk ⟦b⟧ := congrArg Discrete.mk h
                              let one : Discrete.mk as ⟶ ⟨as⟩ := 𝟙 ( Discrete.mk as)
                              let two : Discrete.mk as ⟶ ⟨bs⟩ := one
                              exact one
    map_id := sorry
    map_comp := sorry
  }

#check Discrete.mk

def arxTolax :  (C ⟶ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := sorry


def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := sorry
  unit  := sorry
  counit := sorry


end AdjCC


end CategoryTheory
