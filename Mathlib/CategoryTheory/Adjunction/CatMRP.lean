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

private def relzz (f : a ⟶ b) : isConnectedByZigZag a b := EqvGen.rel _ _ (⟨f, trivial⟩)


lemma transportExt  (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w
  case trans f g => exact EqvGen.trans _ _ _ f g


def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected


private def relsetoid (f : a ⟶ b) : EqvGen isConnectedByZigZag a b := EqvGen.rel _ _ (relzz f )

-- Transport d'un x vers sa composante
def toCC (x : C) : Quotient (@catisSetoid C) := Quotient.mk (@catisSetoid C) x

private def releqq (f : a ⟶ b) : toCC a = toCC b := Quot.EqvGen_sound (relsetoid f)


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

-- Subsingleton.elim
def fmap2 {a b : ↑C} (fct : connectedComponents.obj C ⟶ X)
            (f : a ⟶ b) : (Discrete.mk (fct ⟦a⟧) ⟶ Discrete.mk (fct ⟦b⟧)) :=
           Discrete.eqToHom (congrArg fct (releqq f))


/- The functor for connected components -/
-- look at this ugly map !! VS the commited one
-- look at this ugly map !!
-- look at this ugly map !!
-- look at this ugly map !!
-- look at this ugly map !!

def laxToarx : (connectedComponents.obj C ⟶ X) → (C ⟶ typeToCat.obj X) := fun fct =>
  { obj := fun x => x |> Quotient.mk (@catisSetoid C) |> fct |> Discrete.mk
    map := fun {a b} f => by  simp
                              have := Quot.sound (relzz f)
                              have h : fct ⟦a⟧  = fct ⟦b⟧  := congrArg fct this
                              let one  := 𝟙 ( Discrete.mk (fct ⟦a⟧ ))
                              nth_rewrite 2  [h] at one
                              exact one
    map_id := by simp
    map_comp := by simp;
                   intro x y z f g
                   -- PB

                   sorry
  }

#check Discrete.mk

def arxTolax :  (C ⟶ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := sorry


-- used below, bad, cf eqToHom
def rwmorph {a b x : C} (h : x = a ) (f : a ⟶ b)  : x ⟶ b := by rw [h]; exact f


-- def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
--   homEquiv  := fun C X  ↦ {
--     toFun := laxToarx X C
--     invFun  := arxTolax X C
--     left_inv  := linverse' X C --: LeftInverse invFun toFun
--     right_inv  := rinverse' X C  --: RightInverse invFun toFun
--     }
--   unit : 𝟭 Cat ⟶ connectedComponents ⋙ typeToCat :=
--     {
--       -- 3 different ways of app
--       app:= fun C  ↦ laxToarx _ _ (𝟙 (ccSet C))

--       -- app:= fun C  ↦  { obj := fun x => x |> Quotient.mk (@catisSetoid C) |> Discrete.mk
--       --                   map := fun {a b} f => Discrete.eqToHom ( (releqq f))
--       --                   map_id := by simp
--       --                   map_comp := by simp
--       --                 }

--       --app:= fun C  ↦ laxToarx (ccSet C) C (𝟙 (ccSet C))
--       -- app:= fun C  ↦ {
--       --     obj := fun c => c |> toCC |> Discrete.mk
--       --     map := fun {a b} f => by simp; rw [releqq f]; exact 𝟙 _
--       --     map_id := by simp
--       --     map_comp := fun f g => by have :=releqq f ; have := releqq g; aesop_cat
--       --     }
--     }
--   counit : typeToCat ⋙ connectedComponents ⟶ 𝟭 (Type u) :=  {
--       app := fun X => arxTolax X (typeToCat.obj X) (𝟙 (typeToCat.obj X) : typeToCat.obj X ⥤ typeToCat.obj X)
--       naturality := fun X Y f => by
--         funext xcc
--         obtain ⟨x,h⟩ := quotDecomp xcc
--         aesop_cat
--    }
--   homEquiv_unit := fun {C X F} => by simp;
--                                      apply Functor.hext
--                                      · exact fun x => by rfl
--                                      · exact fun x y f => sorry  --HEq ((laxToarx X C F).map f)   -- (laxToarx X C F).map f  = identite
--                                                                 --     ((laxToarx (connectedComponents.obj C) C (𝟙 (ccSet C)) ≫ Discrete.functor (Discrete.mk ∘ F)).map f)
--   homEquiv_counit := sorry --  : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by aesop_cat


end AdjCC


end CategoryTheory
