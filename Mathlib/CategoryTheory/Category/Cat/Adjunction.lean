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



## Notes
All this could be made with 2-functors

## TODO

Define the left adjoint `Cat.connectedComponents`, which map
a category to its set of connected components.

-/

universe v u
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
  homEquiv  := typeToCatObjectsAdjHomEquiv
  unit := { app:= fun _  ↦ Discrete.mk }
  counit := {
    app := typeToCatObjectsAdjCounitApp
    naturality := fun _ _ _  ↦  Functor.hext (fun _ ↦ rfl)
      (by intro ⟨_⟩ ⟨_⟩ f
          obtain rfl := Discrete.eq_of_hom f
          aesop_cat ) }


section AdjCC


section adjunctionCC
variable (X : Type u)
variable (C D : Cat)

def fnToFctr : (connectedComponents.obj C ⟶ X) → (C ⥤ typeToCat.obj X) := fun fct =>
  { obj := fun x => x |> toCC |> fct |> Discrete.mk
    map := fun f => releqq f |> congrArg fct |> Discrete.eqToHom
    map_id := by simp
    map_comp := by simp
  }


def fctrToFn :  (C ⥤ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := fun fctr  =>
  Quotient.lift (s:= (@catisSetoid C))
     (fun c => (fctr.obj c).as)
     (fun _ _ h => eq_of_zigzag X (transportZigzag fctr h))

set_option linter.longLine false

private def linverse' : Function.LeftInverse (fctrToFn X C ) (fnToFctr X C ) :=
  fun (f : connectedComponents.obj C ⟶ X) => by
    funext xcc
    obtain ⟨x,h⟩ := Quotient.exists_rep xcc
    calc
      fctrToFn X C (fnToFctr X C f) xcc =  fctrToFn X C (fnToFctr X C f) ⟦x⟧ := by rw [<- h]
      _  = ((fnToFctr X C f).obj x).as := rfl
      _  = f ⟦x⟧ := rfl
      _  = f xcc := by rw [h]

private def rinverse' : Function.RightInverse (fctrToFn X C ) (fnToFctr X C ) :=
  fun (fctr : C ⥤ (typeToCat.obj X)) => by
    fapply Functor.hext
    · intro c; rfl
    · intro c d f
      have cdeq : fctr.obj c = fctr.obj d := f |> fctr.map |> Discrete.eq_of_hom |> congrArg Discrete.mk
      let ident : (discreteCategory X).Hom (fctr.obj c) (fctr.obj d) := by rw [cdeq]; exact 𝟙 _
      let p := Subsingleton.helim rfl ident ((fnToFctr X C (fctrToFn X C fctr)).map f)
      exact (p.symm).trans (Subsingleton.helim rfl ident (fctr.map f) : HEq ident (fctr.map f))




def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := fun C X  ↦ {
    toFun := fnToFctr X C
    invFun  := fctrToFn X C
    left_inv  := linverse' X C
    right_inv  := rinverse' X C
    }
  unit : 𝟭 Cat ⟶ connectedComponents ⋙ typeToCat := { app:= fun C  ↦ fnToFctr _ _ (𝟙 (ccSet C)) }
  counit : typeToCat ⋙ connectedComponents ⟶ 𝟭 (Type u) :=  {
      app := fun X => fctrToFn X (typeToCat.obj X) (𝟙 (typeToCat.obj X) : typeToCat.obj X ⥤ typeToCat.obj X)
      naturality := fun X Y f => by
        funext xcc
        obtain ⟨x,h⟩ := Quotient.exists_rep xcc
        aesop_cat
   }
  homEquiv_unit := fun {C X h} => Functor.hext (fun _ => by rfl) (fun _ _ _ => by rfl)
  homEquiv_counit := fun {C X G} => by funext cc;obtain ⟨_,_⟩ := Quotient.exists_rep cc; aesop_cat


end adjunctionCC

end AdjCC


end CategoryTheory.Cat
