
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
def prodMorEq (x x': C) (y y': D)  (f : x ⟶ x') (f' : x ⟶ x') (g : y ⟶ y') (g' : y ⟶ y')  (h : f = f') ( hd: g = g'): (f, g) = (f',g') := by aesop
end additionalstuff

set_option trace.aesop.proof true

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
      eqToHom (h_obj s m h x) ≫ (lift s).map f ≫ eqToHom (h_obj s m h y).symm :=
      by
        let othermap := (eqToHom (h_obj s m h x) ≫ (lift s).map . ≫ eqToHom (h_obj s m h y).symm)
        let mf := m.map f
        let otherf := othermap f
        have  one : (mf).1 = (otherf).1 := sorry
        have  two : (mf).2 = (otherf).2 := sorry
        apply prodObjEq
        . exact one
        . exact two





---------------------------------------------------------------------------------------------------------------------- TEST

-- il faudrait pouvour acceder aux fleches sans leurs domaines / codomaines
-- aka considerer les fleches de x -> y non pas comme des elements du type x -> Y
-- mais comme des elements d'un span non typé dans set.
def aux : ∀ x y f, m.map f =   eqToHom (h_obj s m h x) ≫ (lift s).map f ≫ eqToHom (h_obj s m h y).symm := sorry


end proof

def isLimit (X Y : Cat) : IsLimit (productCone X Y) where
   lift s : s.pt ⥤ Cat.of (X × Y) := lift s
   fac s
    | ⟨WalkingPair.left⟩ =>  rfl
    | ⟨WalkingPair.right⟩ => rfl

   -- on se donne deux foncteurs, one : s.pt -> X et two : s.pt -> Y
   -- on se donne un morphisme, m : s.pt -> X × Y qui verifie
   -- m ≫ fst = one  et  m ≫ snd = two
   -- on veut que m = prod' one two

   -- s : Cone (pair X Y)  -- moralement  one : s.pt -> X et two : s.pt -> Y
   -- m : s.pt ⟶ (productCone X Y).pt  -- moralement m : s.pt -> X × Y
   -- h : ∀ (j : Discrete WalkingPair), m ≫ (productCone X Y).π.app j = s.π.app j  -- moralement m ≫ fst = one  et  m ≫ snd = two
   uniq s m h := by
      dsimp
      -- ⊢ m = Functor.prod' (BinaryFan.fst s) (BinaryFan.snd s)
      have h2 : m = Functor.prod' (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) := by
        exact Functor.ext
                  ( h_obj s m h )
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

                    --have g : m.map f =  eqToHom ⋯ ≫  (Functor.prod' (s.π.app { as := WalkingPair.left }) (s.π.app { as := WalkingPair.right })).map f ≫ eqToHom ⋯ := sorry
                    -- il faudrait enlever les morphismes avant et appres pour la meme strategie que h_obj pour les objets
                    dsimp
                    apply prodMorEq
                    . have mxToProd1 : (m.obj x).1 = (BinaryFan.fst s).obj x :=  prodObjEqFst (h := mxToProd)
                      have myToProd2 : (m.obj y).2 = (BinaryFan.snd s).obj y :=  prodObjEqSnd (h := myToProd)
                      sorry
                    . sorry)
      exact h2

--CategoryTheory.Functor.ext.{v₁, v₂, u₁, u₂} {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂} [Category.{v₂, u₂} D]
-- ext {F G : C ⥤ D}
--  (h_obj : ∀ X, F.obj X = G.obj X)
--  (h_map : ∀ X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm  ) :

-- => peut etre faut il passer par une prop de prod' plutot que par une extensionalité

instance : ChosenFiniteProducts Cat where
  product (X Y : Cat) :  LimitCone (pair X Y) := {cone := (productCone X Y  : Cone (pair X Y)), isLimit := isLimit X Y}
  terminal : LimitCone (Functor.empty Cat) := {cone := asEmptyCone One, isLimit := OneIsTerminal}


end CategoryTheory
