/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Combinatorics.Quiver.ConnectedComponent

universe v u
namespace CategoryTheory.Cat

variable {C D : Cat}
variable {a b c : C}
variable (F : C ⥤ D)

/-! # Relation induced by a category

A category induces a relation on its objects
Two objects are connected if there is an arrow between them.
This relation is not an equivalence, as only reflexivity holds in general.
-/
def isConnected (a : C ) (b : C) : Prop := Nonempty (a ⟶ b)

/-- a morphism `f : a ⟶ b` is a witness that `a` is connected to `b` -/
def connect (f : a ⟶ b) : isConnected a b := Nonempty.intro f

/-- The relation is transported by functors -/
lemma transport (F : C ⥤ D) (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
  obtain ⟨f⟩ := h
  exact ⟨F.map f⟩

/-! ## Equivalence relation induced by a category

To make the previous relation is not an equivalence.
One can take its equivalence closure, under which two objects are connected
iif there is a zigzag of arrows between them.
-/
abbrev isConnectedByZigZag : C → C → Prop := EqvGen isConnected
abbrev isConnectedByZigZag' (C:Cat) : Setoid C := Quiver.zigzagSetoid C


private def connectByZigZag (f : a ⟶ b) : isConnectedByZigZag a b := connect f |>  EqvGen.rel _ _

lemma transportZigZag (h : isConnectedByZigZag a b) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w
  case trans f g => exact EqvGen.trans _ _ _ f g


-- lemma transportZigZag':  ((isConnectedByZigZag' C).r a b) -> (isConnectedByZigZag' D).r (F.obj a) (F.obj b)
--   | ⟨h⟩ => (match h with
--             | .nil =>  Quiver.Path.nil
--             | .cons p f =>
--                 match f with
--                 | Sum.inl f => Quiver.Path.cons (transportZigZag' ⟨p⟩) (Sum.inl (F.map f))
--                 | Sum.inr f =>  Quiver.Path.cons (transportZigZag' ⟨p⟩) (Sum.inr (F.map f)))
--           |> Nonempty.intro

lemma transportZigZag':  ((isConnectedByZigZag' C).r a b) -> (isConnectedByZigZag' D).r (F.obj a) (F.obj b)
  | ⟨h⟩ => by induction h
              · exact Nonempty.intro Quiver.Path.nil
              · sorry


--- Quotient based computation
def catisSetoid (C :Cat) : Setoid C := EqvGen.Setoid isConnected

#check fun (C :Cat)  => C.str.toQuiver

-- Ensemble des composantes d'une categorie
abbrev ccSet  (C : Cat) := Quotient (catisSetoid C)
abbrev wccSet  (C : Cat) := Quiver.WeaklyConnectedComponent C

-- Transport d'un x vers sa composante
def toCC (x : C) : ccSet C := Quotient.mk (catisSetoid C) x
def toCC' (x : C): wccSet C := Quotient.mk (Quiver.zigzagSetoid C) x


private def fmap {X Y : Cat} (F : X ⟶ Y) : (ccSet X) → (ccSet Y) :=
  Quotient.lift
    (s:= catisSetoid X)
    (toCC ∘ F.obj  : X → ccSet Y)
    (fun _ _ => Quot.sound ∘ transportZigZag F )


private abbrev liftedMk {α} (s : Setoid α)  :=
  Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)


/- The functor for connected components -/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ccSet C -- maps a category to its set of CC
  map F := fmap F  -- transport a functor to a function beetwen CC
  map_id X := by calc
      fmap (𝟙 X) =  liftedMk (catisSetoid X) := (rfl : fmap (𝟙 X) = liftedMk (catisSetoid X))
      _          = fun x => x    := funext (fun xt => by obtain ⟨x,h⟩ := Quotient.exists_rep xt
                                                         simp [h.symm])
      _          = 𝟙 (ccSet X)   := by rfl
  map_comp f g := by simp; funext xt; obtain ⟨_,h⟩ := Quotient.exists_rep xt;
                     simp [h.symm];rfl

def releqq (f : a ⟶ b) : toCC a = toCC b := connectByZigZag f |> .rel _ _ |> Quot.EqvGen_sound


def eq_of_zigzag (X) {a b : typeToCat.obj X } (h : isConnectedByZigZag a b) : a.as = b.as := by
  induction h with
  | rel _ _ h => let ⟨f⟩ := h;exact Discrete.eq_of_hom f
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

def transportZigzag (F : C ⥤ D) (h : isConnectedByZigZag a b)
             : isConnectedByZigZag (F.obj a) ( F.obj b) := by
  induction h with
  | rel _ _ h => let ⟨f⟩ := h; exact EqvGen.rel _ _  ⟨F.map f⟩
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2


end CategoryTheory.Cat
