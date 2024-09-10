import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Cones

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
  π : (const J).obj pt ⟶ F

@[ext]
structure MyConeMorphism  {F : J ⥤ M} (x y : MyCone F) where
  hom : x.pt ⟶ y.pt

instance : Category (MyCone F) where
  Hom x y:=  MyConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

def myPostCompose {F G : J ⥤ M} (α : F ⟶ G) : MyCone F ⥤ MyCone G  where
  obj c :=  {pt := c.pt, π := c.π  ≫ α }
  map {X Y} m := { hom := m.hom }

def eqobj {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : ∀ (X : MyCone F),
  (myPostCompose (α ≫ β)).obj X =  (myPostCompose α ⋙ myPostCompose β).obj X := fun _ =>
  MyCone.ext rfl (by simp;exact (Category.assoc _ _ _).symm)

/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
def myPostComposeComp {G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) :
    myPostCompose (α ≫ β) = myPostCompose α ⋙ myPostCompose β :=
    have eqobj := eqobj α β
    Functor.ext eqobj
      (fun c d (m : c ⟶ d) => by
        apply MyConeMorphism.ext
        have res : ((myPostCompose (α ≫ β)).map m).hom =
            (eqToHom (eqobj c ) ≫ (myPostCompose α ⋙ myPostCompose β).map m ≫ eqToHom (eqobj d).symm).hom
          := sorry
        sorry)



/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
def ext {c c' : Cone F} (φ : c.pt = c'.pt)
    (w : ∀ j, c.π.app j = eqToHom φ ≫ c'.π.app j := by aesop_cat) : c ≅ c' where
  hom := { hom := eqToHom φ }
  inv :=
    { hom := eqToHom φ.symm
      w := fun j =>  (eqToHom_comp_iff _ _ _).mpr (w j) }

-- def ext' {c c' : Cone F} (φ : c.pt = c'.pt)
--     (w : ∀ j, c.π.app j = c'.π.app j := by aesop_cat) : c = c' := by
--     sorry



-- -- def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
-- --     postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
-- --   NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

-- def eqobj2 {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : ∀ (X : MyCone F),
--   (myPostCompose α ⋙ myPostCompose β).obj X = (myPostCompose (α ≫ β)).obj X := fun _ =>
--   MyCone.ext rfl (by simp;exact Category.assoc _ _ _)


-- theorem wedgeHomCom {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : myPostCompose α ⋙ myPostCompose β = myPostCompose (α ≫ β) := by
--   have eqobj := eqobj2 α β
--   apply Functor.ext
--   · intro w z m
--     let asfa :=  (myPostCompose α ⋙ myPostCompose β).map m
--     let asfaqw :=  eqToHom (eqobj w) ≫ (myPostCompose (α ≫ β)).map m ≫ eqToHom (eqobj z).symm
--     sorry
--   · exact eqobj

-- theorem wedgeHomCom2 {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : myPostCompose α ⋙ myPostCompose β = myPostCompose (α ≫ β) := by
--   have eqobj := eqobj α β
--   apply Functor.ext
--   · intro w z m
--     simp
--     apply MyConeMorphism.ext

--     have res : ((myPostCompose β).map ((myPostCompose α).map m)).hom =
--         (eqToHom (eqobj w ) ≫ (myPostCompose (α ≫ β)).map m ≫ eqToHom (eqobj z).symm ).hom  :=  sorry -- (g1.trans g2.symm).trans g3.symm
--     exact res
--   -- · sorry


-- def assocOK : ∀ { S F G H  : J ⥤ M} (α : S ⟶ F) (β : F ⟶ G) ( γ : G ⟶ H),
--     (α  ≫ β ) ≫ γ = α ≫ β ≫ γ
--   := by aesop

-- def assocEVIL : ∀ { F G H  : J ⥤ M} (pt : M) (cone : (const J).obj pt ⟶ F) (β : F ⟶ G) (γ : G ⟶ H),
--     (cone  ≫ β ) ≫ γ = cone ≫ β ≫ γ
--   := by aesop


end CategoryTheory




#min_imports
