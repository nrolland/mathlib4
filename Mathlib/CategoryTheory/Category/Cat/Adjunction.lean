/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat.Relation

/-!
# Adjunctions related to Cat, the category of categories

The embedding `typeToCat: Type ⥤ Cat`, mapping a type to the corresponding discrete category, is
left adjoint to the functor `Cat.objects`, which maps a category to its set of objects.

Another functor `connectedComponents : Cat ⥤ Type` maps a category to the set of its connected
components and functors to functions between those sets.

## Notes
All this could be made with 2-functors

-/

universe u
namespace CategoryTheory.Cat

variable (X : Type u) (C : Cat)

private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun f x := f.obj ⟨x⟩
  invFun := Discrete.functor
  left_inv F := Functor.ext (fun _ ↦ rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)
  right_inv _ := rfl

private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

/-- `typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type` -/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects where
  homEquiv := typeToCatObjectsAdjHomEquiv
  unit := { app:= fun _  ↦ Discrete.mk }
  counit := {
    app := typeToCatObjectsAdjCounitApp
    naturality := fun _ _ _  ↦  Functor.hext (fun _ ↦ rfl)
      (by intro ⟨_⟩ ⟨_⟩ f
          obtain rfl := Discrete.eq_of_hom f
          aesop_cat ) }


/-- The connected components functor -/
def connectedComponents.{v} : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F :=
    Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj)
      (fun _ _ ↦ Quot.sound ∘ zigzag_obj_of_zigzag F)
  map_id _ := funext fun x ↦ (Quotient.exists_rep x).elim (fun _ h ↦ by simp [<- h]; rfl)
  map_comp _ _ := funext fun x ↦ (Quotient.exists_rep x).elim (fun _ h => by simp [<- h])


private def fnToFctr  {X C} (fct : connectedComponents.obj C ⟶ X) : (C ⥤ typeToCat.obj X) where
  obj :=  Discrete.mk ∘ fct ∘ Quotient.mk (Zigzag.setoid _)
  map :=  Discrete.eqToHom ∘ congrArg fct ∘ Quotient.sound ∘ Zigzag.of_hom

private def fctrToFn {X} {C : Cat} (fctr :C ⥤ typeToCat.obj X)  : (connectedComponents.obj C ⟶ X) :=
  Quotient.lift
    (fun c => (fctr.obj c).as)
    (fun _ _ h => eq_of_zigzag X (zigzag_obj_of_zigzag fctr h))

/-- `typeToCat : Type ⥤ Cat` is right adjoint to `connectedComponents : Cat ⥤ Type` -/
def connectedComponentsTypeToCatAdj : connectedComponents ⊣ typeToCat where
  homEquiv C X := {
    toFun := fnToFctr
    invFun := fctrToFn
    left_inv := fun f ↦ funext fun x ↦ by
      obtain ⟨x, h⟩ := Quotient.exists_rep x
      rw [← h]
      rfl
    right_inv  := fun fctr ↦
      Functor.hext (fun _ ↦ rfl) (fun c d f ↦
        have : Subsingleton (fctr.obj c ⟶ fctr.obj d) := Discrete.instSubsingletonDiscreteHom _ _
        (Subsingleton.elim (fctr.map f) _).symm.heq) }
  unit := { app:= fun C  ↦ fnToFctr (𝟙 _) }
  counit :=  {
      app := fun X => fctrToFn (𝟙 typeToCat.obj X)
      naturality := fun _ _ _ =>
        funext (fun xcc => by
          obtain ⟨x,h⟩ := Quotient.exists_rep xcc
          aesop_cat) }
  homEquiv_unit := fun {C X h} => Functor.hext (fun _ => by rfl) (fun _ _ _ => by rfl)
  homEquiv_counit := fun {C X G} => by funext cc;obtain ⟨_,_⟩ := Quotient.exists_rep cc; aesop_cat


end CategoryTheory.Cat
