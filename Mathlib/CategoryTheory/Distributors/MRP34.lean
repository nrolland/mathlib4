import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Category.Cat

set_option linter.longLine false

open CategoryTheory
open Functor

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {M : Type vm } [Category.{um} M]

structure Simple (F : J ⥤ M) where
  pt : M

structure SimpleMorphism  {F : J ⥤ M} (x y : Simple F) where
  hom : x.pt ⟶ y.pt

instance  simple (F : J ⥤ M) : Category (Simple F) where
  Hom x y:=  SimpleMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

variable {F G H: J ⥤ M}
variable {X Y: Simple F}

def simpleCompose  (α : F ⟶ G) : Simple F ⥤ Simple G  where
  obj c :=  { pt := c.pt  }
  map {X Y} (m : X ⟶ Y) := { hom := m.hom }

-- Definitional equality of type
example (α : F ⟶ G) (β : G ⟶ H) :
    ((simpleCompose (α ≫ β)).obj X ⟶ (simpleCompose (α ≫ β)).obj Y)
    = ((simpleCompose α ⋙ simpleCompose β).obj X ⟶ (simpleCompose α ⋙ simpleCompose β).obj Y)
  := rfl

-- Definitional equality of type
example (α : F ⟶ G) (β : G ⟶ H) :
    ((simpleCompose (α ≫ β)).obj X ⟶ (simpleCompose (α ≫ β)).obj Y)
    = ((simpleCompose α ⋙ simpleCompose β).obj X ⟶ (simpleCompose α ⋙ simpleCompose β).obj Y)
  := rfl

example (α : F ⟶ G) (β : G ⟶ H) : (((simpleCompose (α ≫ β)).obj X)) =  ((simpleCompose α ⋙ simpleCompose β).obj X) := rfl



------

structure MyCone  (F : J ⥤ M) where
  pt : M
  π : (const J).obj pt ⟶ F

structure MyConeMorphism   (x y : MyCone F) where
  hom : x.pt ⟶ y.pt

instance : Category (MyCone F) where
  Hom x y:=  MyConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

def myPostCompose   (α : F ⟶ G) : MyCone F ⥤ MyCone G  where
  obj c :=  {pt := c.pt, π := c.π  ≫ α }
  map {X Y} m := { hom := m.hom }

variable {X Y: MyCone F}

example (α : F ⟶ G) (β : G ⟶ H) : (((myPostCompose (α ≫ β)).obj X)) =  ((myPostCompose α ⋙ myPostCompose β).obj X) := rfl

example (α : F ⟶ G) (β : G ⟶ H) :
    ((myPostCompose (α ≫ β)).obj X ⟶ (myPostCompose (α ≫ β)).obj Y) =
    ((myPostCompose α ⋙ myPostCompose β).obj X ⟶ (myPostCompose α ⋙ myPostCompose β).obj Y)
  := rfl
