/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
/-!
`Cat` is a category on its own, views categories as its objects and functors as its morphism.

On one hand, we can build a cartesian product category out of a pair of categories.
On the other hand `Cat`, as a category, comes with its own definition for an object to be a product.

We verify here that the product *in* `Cat` is given by the product *of* categories, when viewed
as an object.
-/

universe v u

namespace CategoryTheory

namespace Cat

open Limits

/-- The chosen terminal object in `Cat`. -/
abbrev OneCat : Cat := Cat.of (ULift (ULiftHom (Discrete Unit)))

example : OneCat := ⟨⟨⟨⟩⟩⟩

/-- The chosen terminal object in `Cat` is terminal. -/
def isTerminalPUnit : IsTerminal OneCat :=
  IsTerminal.ofUniqueHom (fun _ ↦ (Functor.const _).obj ⟨⟨⟨⟩⟩⟩) fun _ _ ↦ rfl

/-- The chosen product of categories `C × D` yields a product cone in `Cat`. -/
def prodCone (C D : Cat.{v,u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

/-- The product cone in `Cat` is indeed a product. -/
def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => S.fst.prod' S.snd) (fun _ => rfl) (fun _ => rfl) (fun _ _ h1 h2 =>
    Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))

instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) := { isLimit := isLimitProdCone X Y }
  terminal  := { isLimit := isTerminalPUnit }

example : MonoidalCategory Cat := by infer_instance

example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

-- some lemmas about the monoidal structure generated by the finite product-

variable (C : Cat) (D : Cat)

@[simp]
lemma leftUnitor_is_snd (C : Cat) :
    (λ_ C).hom = Prod.snd _ _  := rfl

@[simp]
lemma leftUnitor_inv_is_sectionr (C : Cat) :
    (λ_ C).inv = Prod.sectr ⟨⟨⟨⟩⟩⟩ _  := rfl

@[simp]
lemma rightUnitor_is_fst (C : Cat) :
    (ρ_ C).hom = Prod.fst _ _  := rfl

@[simp]
lemma rightUnitor_inv_is_sectionl (C : Cat) :
    (ρ_ C).inv = Prod.sectl _ ⟨⟨⟨⟩⟩⟩  := rfl

@[simp]
lemma whiskerLeft_is_product_with_identity_left (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    MonoidalCategoryStruct.whiskerLeft X f = (𝟭 X).prod f   := rfl

@[simp]
lemma whiskerRight_is_product_with_identity_right {A : Cat} {B : Cat} (f : A ⟶ B)  (X : Cat) :
    MonoidalCategoryStruct.whiskerRight f X  = f.prod (𝟭 X)   := rfl


end Monoidal


end CategoryTheory
