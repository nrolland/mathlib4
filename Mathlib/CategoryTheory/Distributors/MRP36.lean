import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Const

open CategoryTheory

universe v₁ vm u₁ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {M : Type um } [Category.{vm} M]
variable {F G H: J ⥤ M} (α : F ⟶ G) (β : G ⟶ H)

@[ext]
structure MyCone  (F : J ⥤ M) where
  pt : M
  π : (Functor.const J).obj pt ⟶ F

structure MyConeMorphism   (x y : MyCone F) where
  hom : x.pt ⟶ y.pt

instance : Category (MyCone F) where
  Hom x y:=  MyConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

def pc (α : F ⟶ G) : MyCone F ⥤ MyCone G  where
  obj c :=  {pt := c.pt, π := c.π  ≫ α }
  map {X Y} m := { hom := m.hom }

def eqobj  (x : MyCone F):
    (((pc (α ≫ β)).obj x)) =  ((pc α ⋙ pc β).obj x) :=
  MyCone.ext rfl (by simp;exact (Category.assoc _ _ _).symm)

---------------------------------------------------------------------
-- We want (pc (α ≫ β)).map m  = (pc α ⋙ pc β).map m
-- but that's not type correct, so we need instead

def howToGetThat? (x y : MyCone F) (m : x ⟶ y) :
   eqToHom (eqobj _ _ x ) ≫ ((pc α ⋙ pc β).map m) = ((pc (α ≫ β)).map m ≫ eqToHom (eqobj _ _ y))
   := sorry

def howToGetThat (x y : MyCone F) (m : x ⟶ y) :
    (pc (α ≫ β)).map m = cast (by simp[eqobj]) ((pc α ⋙ pc β).map m)
  := by
    simp
    rw [Category.assoc]
    sorry

---------------------------------------------------------------------
-- PS : with bounded definitional equality, it would be easy as it has the same definition
def eq1 (x y: MyCone F) (m : x ⟶ y) :
  (pc (α ≫ β)).map m = { hom := m.hom }  := rfl

def eq2 (x y: MyCone F) (m : x ⟶ y) :
   (pc α ⋙ pc β).map m = { hom := m.hom }  := rfl
