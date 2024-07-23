
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

open Limits

/-- The chosen terminal object in `Cat`. -/
abbrev One.{u} : Cat.{u} := Cat.of (Discrete PUnit.{u+1})

/-- The chosen terminal object in `Cat` is terminal. -/
def OneIsTerminal : IsTerminal One where
  lift s := Functor.star s.pt
  fac s (j : Discrete PEmpty.{1}) := by dsimp; exact PEmpty.elim j.as
  uniq s m _ :=  Functor.punit_ext' m (Functor.star s.pt)


section additionalstuff
universe  v₂ v₃  u₂ u₃
variable  (C : Type u₂) [Category.{v₂,u₂} C] (D : Type u₃)[Category.{v₃,u₃} D]
/-- The equality between `(X.1, X.2)` and `X`. -/
def prodObjEq (x : C) (x' : C) (y: D)(y': D)  (h : x = x') (g : y = y'): (x, y) = (x',y') := by aesop
def prodObjEqFst (x : C) (x' : C) (y: D) (y': D) (h : (x, y) = (x',y')) : x = x' := by aesop
def prodObjEqSnd (x : C) (x' : C) (y: D) (y': D) (h : (x, y) = (x',y')) : y = y' := by aesop
end additionalstuff

def productCone.{u,v} (C : Cat.{u,v} ) (D : Cat.{u,v}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)

section proof
universe v u
variable {C D : Cat.{u,v}}
variable (s : Cone (pair C D ))
variable (m : s.pt ⟶ (productCone  C D ).pt)
variable (h : ∀ (j : Discrete WalkingPair), (m ≫ (productCone C D).π.app j = s.π.app j))

def lift : s.pt ⥤ Cat.of (C × D) := Functor.prod' (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)

def h_obj (x : s.pt) : m.obj x = (lift s).obj x  :=
  by
    apply prodObjEq
    . rw [<- h ⟨WalkingPair.left⟩]; rfl
    . rw [<- h ⟨WalkingPair.right⟩]; rfl

def h_map (x : s.pt) (y : s.pt) (f : x ⟶ y ): m.map f =
      eqToHom (h_obj s m h x) ≫ (lift s).map f ≫ eqToHom (h_obj s m h y).symm :=  by
        have  one : ( m.map f).1 = ((eqToHom (h_obj s m h x) ≫ (lift s).map f ≫ eqToHom (h_obj s m h y).symm)).1 :=
          have lem1 : (m.map f).1 = (m ≫ (productCone C D).π.app { as := WalkingPair.left }).map f  := rfl
          have lem2 : m ≫ (productCone C D).π.app { as := WalkingPair.left } = s.π.app { as := WalkingPair.left } := h ⟨WalkingPair.left⟩
          sorry
        have  two : (m.map f).2 = (((eqToHom (h_obj s m h x) ≫ (lift s).map f ≫ eqToHom (h_obj s m h y).symm))).2 := sorry

        apply prodObjEq
        . exact one
        . exact two

end proof



def isLimit (X Y : Cat) : IsLimit (productCone X Y) where
   lift s : s.pt ⥤ Cat.of (X × Y) := lift s
   fac s
    | ⟨WalkingPair.left⟩ =>  rfl
    | ⟨WalkingPair.right⟩ => rfl
   uniq s m h :=  Functor.ext (h_obj s m h) (h_map s m h)

instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) :  LimitCone (pair X Y) := {cone := (productCone X Y  : Cone (pair X Y)), isLimit := isLimit X Y}
  terminal : LimitCone (Functor.empty Cat) := {cone := asEmptyCone One, isLimit := OneIsTerminal}


end CategoryTheory
