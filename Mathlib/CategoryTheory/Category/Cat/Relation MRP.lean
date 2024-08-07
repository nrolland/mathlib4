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



/-! ## Equivalence relation induced by a category

To make the previous relation is not an equivalence.
One can take its equivalence closure, under which two objects are connected
iif there is a zigzag of arrows between them.
-/

def isConnected (a : C ) (b : C) : Prop := Nonempty (a ⟶ b)
abbrev isConnectedByZigZag : C → C → Prop := EqvGen (isConnected)

abbrev isConnectedByZigZag' (C:Cat) : Setoid C := Quiver.zigzagSetoid C

def transportZigzag (h : isConnectedByZigZag a b) : isConnectedByZigZag (F.obj a) ( F.obj b) :=
  h.rec (fun  _ _ h => h.elim (fun f =>  EqvGen.rel _ _  ⟨F.map f⟩))
    (fun _ => EqvGen.refl _)
    (fun _ _ _ ih => EqvGen.symm _ _ ih)
    (fun  _ _ _ _ _ ih1 ih2 => EqvGen.trans _ _ _ ih1 ih2)

lemma transportZigZag' (haea : (isConnectedByZigZag' C).r a b) : (isConnectedByZigZag' D).r (F.obj a) (F.obj b) := by
  have ⟨p⟩ := haea
  induction p
  case nil => exact ⟨Quiver.Path.nil⟩
  case cons b c p' f ih  =>
    exact (ih ⟨p'⟩).elim (fun pd =>
      f.elim
        (fun f => ⟨Quiver.Path.cons pd (.inl (F.map f))⟩)
        (fun f => ⟨Quiver.Path.cons pd (.inr (F.map f))⟩))


--- Quotient based computation
def catisSetoid (C :Cat) : Setoid C := EqvGen.Setoid isConnected

#check fun (C :Cat)  => C.str.toQuiver

-- Ensemble des composantes d'une categorie
abbrev ccSet  (C : Cat) := Quotient (catisSetoid C)
abbrev wccSet  (C : Cat) := Quotient (Quiver.zigzagSetoid C)

-- Transport d'un x vers sa composante
def toCC (x : C) : ccSet C := Quotient.mk (catisSetoid C) x
def toCC' (x : C): wccSet C := Quotient.mk (Quiver.zigzagSetoid C) x


private def fmap {X Y : Cat} (F : X ⟶ Y) : (wccSet X) → (wccSet Y) :=
  Quotient.lift
    (s:= Quiver.zigzagSetoid X)
    (toCC' ∘ F.obj  : X → wccSet Y)
    (fun _ _ => Quot.sound ∘ transportZigZag' F )


private abbrev liftedMk {α} (s : Setoid α)  :=
  Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)


/- The functor for connected components -/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := wccSet C -- maps a category to its set of CC
  map F := fmap F  -- transport a functor to a function beetwen CC
  map_id X := by calc
      fmap (𝟙 X) =  liftedMk (Quiver.zigzagSetoid X) := (rfl : fmap (𝟙 X) = liftedMk (Quiver.zigzagSetoid X))
      _          = fun x => x    := funext (fun xt => by obtain ⟨x,h⟩ := Quotient.exists_rep xt
                                                         simp [h.symm])
      _          = 𝟙 (wccSet X)   := by rfl
  map_comp f g := by simp; funext xt; obtain ⟨_,h⟩ := Quotient.exists_rep xt;
                     simp [h.symm];rfl

def releqq (f : a ⟶ b) : toCC' a = toCC' b := connectByZigZag' f |> .rel _ _ |> Quot.EqvGen_sound


def eq_of_zigzag (X) {a b : typeToCat.obj X } (h : isConnectedByZigZag a b) : a.as = b.as := by
  induction h with
  | rel _ _ h => let ⟨f⟩ := h;exact Discrete.eq_of_hom f
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2



end CategoryTheory.Cat
