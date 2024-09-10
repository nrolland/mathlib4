import Mathlib.CategoryTheory.Products.Basic

namespace CategoryTheory

open CategoryTheory
open Functor

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : B ⥤ M)
set_option linter.longLine false

@[ext]
structure Cone : Type (max (max um u₂) vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj c

@[ext]
structure ConeMorphism  {F : B ⥤ M} (x y : Cone F) where
  hom : x.pt ⟶ y.pt

instance : Category (Cone F) where
  Hom x y:=  ConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }


-- def postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where
--   obj c :=
--     { pt := c.pt
--       π := c.π ≫ α }
--   map f := { hom := f.hom }

-- def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
--     postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
--   NatIso.ofComponents fun s => Cones.ext (Iso.refl _)


def coneHom {F G : B ⥤ M} (α : F ⟶ G) : Cone F ⥤ Cone G  where
  obj w :=  {pt := w.pt, leg := fun c =>  w.leg c ≫ α.app c }
  map {X Y} m := { hom := m.hom }

def eqobj {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : ∀ (X : Cone F),
  (coneHom α ⋙ coneHom β).obj X = (coneHom (α ≫ β)).obj X := fun _ =>
  Cone.ext rfl (by simp;funext;exact Category.assoc _ _ _)

theorem wedgeHomCom {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : coneHom α ⋙ coneHom β = coneHom (α ≫ β) := by
  have eqobj : ∀ (X : Cone F), (coneHom α ⋙ coneHom β).obj X = (coneHom (α ≫ β)).obj X := eqobj α β
  apply Functor.ext
  · intro w z m
    let asfa : (coneHom α ⋙ coneHom β).obj w ⟶ (coneHom α ⋙ coneHom β).obj z  :=  (coneHom α ⋙ coneHom β).map m
    let asfaqw : (coneHom α ⋙ coneHom β).obj w ⟶ (coneHom (α ≫ β)).obj z :=  eqToHom (eqobj w) ≫ (coneHom (α ≫ β)).map m
    sorry
  · exact eqobj

-- theorem eqToHom_naturality {f g : β → C} (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
--     z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j'


theorem wedgeHomCom2 {F G H : B ⥤ M} (α : F ⟶ G) (β : G ⟶ H) : coneHom α ⋙ coneHom β = coneHom (α ≫ β) := by
  have eqobj := eqobj α β
  apply Functor.ext
  · intro w z m
    simp
    apply ConeMorphism.ext

    have res : ((coneHom β).map ((coneHom α).map m)).hom =
        (eqToHom (eqobj w ) ≫ (coneHom (α ≫ β)).map m ≫ eqToHom (eqobj z).symm ).hom  :=  sorry -- (g1.trans g2.symm).trans g3.symm
    exact res
  -- · sorry

end CategoryTheory


#min_imports
