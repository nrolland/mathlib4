import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Category.Cat


set_option linter.longLine false

open CategoryTheory

universe v₁ vm u₁ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {M : Type um } [Category.{vm} M]
variable {F G H: J ⥤ M}

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

----------------------------------------------------------------------

def eq1 (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
  (pc (α ≫ β)).map m = { hom := m.hom }  := rfl

def eq2 (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   (pc α ⋙ pc β).map m = { hom := m.hom }  := rfl

-- def heq (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
--   HEq ((pc (α ≫ β)).map m) ((pc α ⋙ pc β).map m) := sorry

def eqobj (α : F ⟶ G) (β : G ⟶ H) (x : MyCone F):
    (((pc (α ≫ β)).obj x)) =  ((pc α ⋙ pc β).obj x) :=
  MyCone.ext rfl (by simp;exact (Category.assoc _ _ _).symm)

example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   ((pc α ⋙ pc β).map m) = (eqToHom (eqobj _ _ x ).symm ≫ (pc (α ≫ β)).map m ≫ eqToHom (eqobj _ _ y) )
   :=  sorry

example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   eqToHom (eqobj _ _ x ) ≫ ((pc α ⋙ pc β).map m) = ((pc (α ≫ β)).map m ≫ eqToHom (eqobj _ _ y))
   :=  sorry




def h1 (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   eqToHom (eqobj _ _ x ) ≫ (pc α ⋙ pc β).map m = ({ hom := m.hom } : (pc (α ≫ β)).obj x ⟶ (pc α ⋙ pc β).obj y)  := sorry


def h2 (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   ((pc (α ≫ β)).map m ≫ eqToHom (eqobj _ _ y)) = ({ hom := m.hom } : (pc (α ≫ β)).obj x ⟶ (pc α ⋙ pc β).obj y)  := by
    -- reecrire avec les regles suivantes :
    -- simp_all only [eqToHom_refl, Category.comp_id, Category.id_comp]
    sorry



example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   eqToHom (eqobj _ _ x ) ≫ (pc α ⋙ pc β).map m = ((pc (α ≫ β)).map m ≫ eqToHom (eqobj _ _ y))
   :=  sorry



/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext {F G : J ⥤ M} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm) :
    F = G := by
  match F, G with
  | CategoryTheory.Functor.mk F_pre _ _ , CategoryTheory.Functor.mk G_pre _ _ =>
    match F_pre, G_pre with
    | Prefunctor.mk F_obj _ , Prefunctor.mk G_obj _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simp_all only [eqToHom_refl, Category.comp_id, Category.id_comp]
