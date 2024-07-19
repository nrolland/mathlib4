
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

open Limits

universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable (X : Type u) [Category.{v,u} X] (A : Type u₁)[Category.{v₁,u₁} A] (C : Type u₂) [Category.{v₂,u₂} C] (D : Type u₃)[Category.{v₃,u₃} D]

/-- The chosen terminal object in `Cat`. -/
abbrev One : Cat.{u,u} := Cat.of (Discrete PUnit.{u+1})

/-- The chosen terminal object in `Cat` is terminal. -/
def OneIsTerminal : IsTerminal One where
  lift s := Functor.star s.pt
  fac s (j : Discrete PEmpty.{1}) := by dsimp; exact PEmpty.elim j.as
  uniq s m _ :=  Functor.punit_ext' m (Functor.star s.pt)


def productCone (C D : Cat.{u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _) (Prod.snd _ _)


def t (X Y : Cat) : (productCone X Y).fst = Prod.fst X Y := rfl


/-- The equality between `(X.1, X.2)` and `X`. -/
def prodObjEq (x : C) (x' : C) (y: D)(y': D)  (h : x = x') (g : y = y'): (x, y) = (x',y') := by aesop
def prodObjEqCp1 (x : C) (x' : C) (y: D) (y': D) (h : (x, y) = (x',y')) : x = x' := by aesop
def prodObjEqCp2 (x : C) (x' : C) (y: D) (y': D) (h : (x, y) = (x',y')) : y = y' := by aesop
def prodMorEq (x x': C) (y y': D)  (f : x ⟶ x') (f' : x ⟶ x') (g : y ⟶ y') (g' : y ⟶ y')  (h : f = f') ( hd: g = g'): (f, g) = (f',g') := by aesop



def isLimit (X Y : Cat) : IsLimit (productCone X Y) where
   lift s : s.pt ⥤ Cat.of (X × Y) := Functor.prod' (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
   fac s
    | ⟨WalkingPair.left⟩ =>  rfl
    | ⟨WalkingPair.right⟩ => rfl

   --- PB
   uniq s m h := by
      dsimp
      -- ⊢ m = Functor.prod' (BinaryFan.fst s) (BinaryFan.snd s)
      have h2 : m = Functor.prod' (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) := by
        exact Functor.ext
                  ( --- h_obj : ∀ X, F.obj X = G.obj X  --
                    fun _ => by
                                apply prodObjEq
                                . have h3 := h ⟨WalkingPair.left⟩;
                                  rw [<- h ⟨WalkingPair.left⟩]; rfl
                                . rw [<- h ⟨WalkingPair.right⟩];rfl)
                  ( --- h_map : ∀ X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm
                    fun x y f => by
                  -- En theorie, on veut montrer que m f = (s.fst f, s.snd f)
                  -- c'est equivalent a (m >> fst) f = s.fst f et (m >> snd) f = s.snd f
                  -- or c'est ce que l'on a avec h
                  -- En pratique, ca ne type-check pas..
                  -- l'interface nous demande de montrer m f = mx -> (s.fst x, s.snd x) ---(s.fst f, s.snd f)-> (s.fst y, s.snd y) --> my
                    have mxToProd : m.obj x = ((BinaryFan.fst s).obj x, (BinaryFan.snd s).obj x)  := sorry
                    have myToProd : m.obj y = ((BinaryFan.fst s).obj y, (BinaryFan.snd s).obj y)  := sorry
                    have h3 := h ⟨WalkingPair.left⟩;
                    --rw [<- h ⟨WalkingPair.left⟩] -- ne marche pas ?? (tactic 'rewrite' failed, motive is not type correct)

                    -- il faudrait enlever les morphismes avant et appres pour la meme strategie que h_obj pour les objets
                    apply prodMorEq
                    . have mxToProd1 : (m.obj x).1 = (BinaryFan.fst s).obj x :=  prodObjEqCp1 (h := mxToProd)
                      have myToProd1 : (m.obj y).1 = (BinaryFan.fst s).obj y :=  prodObjEqCp1 (h := myToProd)
                      sorry
                    . sorry)
      exact h2

--CategoryTheory.Functor.ext.{v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂} [Category.{v₂, u₂} D]
-- ext {F G : C ⥤ D}
--  (h_obj : ∀ X, F.obj X = G.obj X)
--  (h_map : ∀ X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm  ) :


instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) :  LimitCone (pair X Y) := {cone := (productCone X Y  : Cone (pair X Y)), isLimit := isLimit X Y}
  terminal : LimitCone (Functor.empty Cat) := {cone := asEmptyCone One, isLimit := OneIsTerminal}


end CategoryTheory
