import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Category.Cat

set_option linter.longLine false

namespace CategoryTheory

open CategoryTheory
open Functor
open Limits.Cones
open Limits

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {M : Type vm } [Category.{um} M]
variable (F : J ⥤ M)

@[ext]
structure MyCone where
  pt : M
  π : (const J).obj pt ⟶ F -- un cone est une tnat depuis un fctr constant

@[ext]
structure MyConeMorphism  {F : J ⥤ M} (x y : MyCone F) where
  hom : x.pt ⟶ y.pt -- un morphisme entre deux cones est un morphisme entre les sommets


example  {x y : MyCone F} : (hom : x.pt ⟶ y.pt) -> MyConeMorphism x y :=  MyConeMorphism.mk

instance : Category (MyCone F) where -- pour un foncteur F, les cones forment une categorie
  Hom x y:=  MyConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

def myPostCompose {F G : J ⥤ M} (α : F ⟶ G) : MyCone F ⥤ MyCone G  where -- un morphisme de foncteur se traduit en un morphisme de categorie
  obj c :=  {pt := c.pt, π := c.π  ≫ α }
  map {X Y} m := { hom := m.hom }


/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
def eqobj {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : ∀ (X : MyCone F),
  (myPostCompose (α ≫ β)).obj X =  (myPostCompose α ⋙ myPostCompose β).obj X := fun _ =>
  MyCone.ext rfl (by simp;exact (Category.assoc _ _ _).symm)

/-- La meme chose sur les morphismes de la categorie des cones de F -- erreur de type -/
-- def eqmap {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) {X Y: MyCone F}: ∀ (m : X ⟶ Y),
--   (myPostCompose (α ≫ β)).map m =  (myPostCompose α ⋙ myPostCompose β).map m := sorry

-- les types en question
def eqmap_type1 {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) {X Y: MyCone F} (m : X ⟶ Y) :
    (myPostCompose (α ≫ β)).obj X ⟶ (myPostCompose (α ≫ β)).obj Y :=
  (myPostCompose (α ≫ β)).map m

def eqmap_type2 {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) {X Y: MyCone F} (m : X ⟶ Y)  :
    (myPostCompose α ⋙ myPostCompose β).obj X ⟶ (myPostCompose α ⋙ myPostCompose β).obj Y :=
 (myPostCompose α ⋙ myPostCompose β).map m

-- On essaye d'avoir une HEq a la place
def heqmap {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) {X Y: MyCone F}: ∀ (m : X ⟶ Y),
  HEq ((myPostCompose (α ≫ β)).map m ) ( (myPostCompose α ⋙ myPostCompose β).map m) := fun m => by
    simp
    have r : ((myPostCompose (α ≫ β)).map m).hom = m.hom := rfl
    have s : ((myPostCompose α ⋙ myPostCompose β).map m).hom = m.hom := rfl
    have t : ((myPostCompose (α ≫ β)).map m).hom = ((myPostCompose α ⋙ myPostCompose β).map m).hom := rfl
    have t' := MyConeMorphism.ext t
    sorry

--- ext ne marche pas car les types sont les meme
example {x y : MyCone F} {m n : MyConeMorphism x y} : m.hom = n.hom → m = n  := MyConeMorphism.ext

--- il faut une version qui produit du HEq
def fct {x y x' y' : MyCone F} (hx : x.pt = x'.pt) (hy : y.pt = y'.pt)
    (m : MyConeMorphism x y) (m' : MyConeMorphism x' y')  :
  (m.hom = m'.hom) → HEq m m' := sorry

def type1  {x y : MyCone F} {m : MyConeMorphism x y} : x.pt ⟶ y.pt := m.hom
def type2  {x' y' : MyCone F} {m' : MyConeMorphism x' y'} : x'.pt ⟶ y'.pt := m'.hom

-- --- Idealement la type error est remplacée
-- --- par un obligation de prouver que ca n'est pas une erreur
-- --- Aka c'est une valeur protégée par une typeclass
-- example  {x y x' y' : MyCone F} {m : MyConeMorphism x y} {m' : MyConeMorphism x' y'} :
--      m.hom = m'.hom → HEq m m'
--   := sorry

/-- This assembles into a functor -/
def myPostComposeComp {G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) :
    myPostCompose (α ≫ β) = myPostCompose α ⋙ myPostCompose β :=
    have eqobj := eqobj α β
    Functor.ext eqobj
      (fun c d (m : c ⟶ d) => by
        apply MyConeMorphism.ext
        have res : ((myPostCompose (α ≫ β)).map m).hom = m.hom := rfl
        have res : m.hom =
            (eqToHom (eqobj c ) ≫ (myPostCompose α ⋙ myPostCompose β).map m ≫ eqToHom (eqobj d).symm).hom
          := sorry
        have res : ((myPostCompose (α ≫ β)).map m).hom =
            (eqToHom (eqobj c ) ≫ (myPostCompose α ⋙ myPostCompose β).map m ≫ eqToHom (eqobj d).symm).hom
          := sorry
        exact res)
-- on n'a pas a = c, b = d, => a -> b = c -> d, ce sont des types differents

--
def Cone :  (J ⥤ M) ⥤ Cat where
  obj f := sorry
  map {f g} α := sorry


end CategoryTheory
