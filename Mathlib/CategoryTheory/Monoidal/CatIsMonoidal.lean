
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

open Limits

noncomputable example : MonoidalCategory Cat := monoidalOfHasFiniteProducts _

universe v u

/-- The chosen terminal object in `Cat`. -/
abbrev chosenTerminalCategory : Cat.{u,u} := Cat.of (Discrete PUnit.{u+1})

def bangFunctor  (C : Cat) : Functor C chosenTerminalCategory where
  obj _ := ⟨PUnit.unit⟩
  map _ := eqToHom rfl
  map_id := by intro _
               dsimp
  map_comp := by intro _ _ _ _ _
                 dsimp
                 rw [Category.comp_id]

/-- The chosen terminal object in `Cat` is terminal. -/
def chosenTerminalCategoryIsTerminal : IsTerminal (chosenTerminalCategory) := {
   lift := fun s ↦ bangFunctor s.pt
   fac := fun s (j : Discrete PEmpty.{1}) ↦ by dsimp -- j can not exist
                                               exact PEmpty.elim j.as
   uniq := sorry
  }


instance productCategory C D [Category C] [Category D] : Category (C × D) where
    Hom := fun ⟨c,d⟩ ⟨c',d'⟩ ↦  (Category.toCategoryStruct.toQuiver.Hom c c') × ( Category.toCategoryStruct.toQuiver.Hom d d')
    id  :=  fun ⟨c,d⟩   ↦  ⟨Category.toCategoryStruct.id c,Category.toCategoryStruct.id d⟩
    comp := fun f g ↦ ⟨Category.toCategoryStruct.comp f.1 g.1,Category.toCategoryStruct.comp f.2 g.2⟩
    id_comp := by intro _ _ ⟨_,_⟩
                  dsimp
                  rw [Category.id_comp, Category.id_comp]
    comp_id := by intro _ _ ⟨_,_⟩
                  dsimp
                  rw [Category.comp_id, Category.comp_id]
    assoc := by intros _ _ _ _ _ _ _
                dsimp
                rw [Category.assoc, Category.assoc]

def product (C : Cat) (D : Cat) : Cat := Cat.of (C × D)
def pi_1 {C : Cat} {D : Cat} : product C D ⥤ C    where
  obj  := fun x ↦ x.1
  map  := fun f ↦ f.1
  map_id := fun (⟨a,_⟩ )  ↦ by dsimp
                               aesop_cat
  map_comp := by aesop_cat

def pi_2 {C : Cat} {D : Cat} : product C D ⥤ D    where
  obj  := fun x ↦ x.2
  map  := fun f ↦ f.2
  map_id := by aesop_cat
  map_comp := by aesop_cat

def productCone (C : Cat.{u}) (D : Cat) : BinaryFan C  D := BinaryFan.mk pi_1 pi_2

def isLimit (X Y : Cat) : IsLimit (productCone X Y) := sorry



-- /-- The category of small categories has all small limits. -/
-- instance : HasLimits Cat.{v, v} where
--   has_limits_of_shape _ :=
--     { has_limit := fun F => ⟨⟨⟨HasLimits.limitCone F, HasLimits.limitConeIsLimit F⟩⟩⟩ }
instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) :  LimitCone (pair X Y) := {cone :=(productCone X Y  : Cone (pair X Y)), isLimit := sorry}
  terminal : LimitCone (Functor.empty Cat) := {cone := asEmptyCone chosenTerminalCategory, isLimit := chosenTerminalCategoryIsTerminal}

--noncomputable
--example : MonoidalCategory Cat := monoidalOfChosenFiniteProducts _

--example : HasTerminal Cat

def one := 1
