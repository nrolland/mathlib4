import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Category.Cat
open CategoryTheory Limits Cones

variable {J M : Type*} [Category J] [Category M]
set_option linter.style.longLine false
set_option linter.docPrime false


def postcomposeCompEqual {F G H : J ⥤ M} (α : F ⟶ G) (β : G ⟶ H) :
    postcompose (α ≫ β) = postcompose α ⋙ postcompose β := by
        fapply CategoryTheory.Functor.ext
        · intro X
          simp [Cones.postcompose]
        · intro X Y f
          ext
          simp
          sorry

-- simp is a very powerful mechanism
def a_niceproof0 (F : J ⥤ M) (X : Cone F) :  (Cones.postcompose (𝟙 F)).obj X =  X :=  by
      simp [Cones.postcompose]

-- lets break that down a bit, and clean some magic
def a_niceproof1 (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=  by
      simp?

-- lets break that down a bit, and clean some magic
def a_niceproof2 (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=  by
      simp only [Category.comp_id]

-- now we can explicit the operations
def a_niceproof_explicit (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=  by -- we want to prove a proposition on two cones
  let nat_gives_coneX : ((Functor.const J).obj X.pt ⟶ F) → Prop := fun α ↦ { pt := X.pt, π := α } = X -- we view the desired proposition on two cones as a statement on a single t-nat
  let comp_id : X.π ≫ 𝟙 F = X.π := Category.comp_id X.π -- we have equality of t-nat which is super strong statement
  let t1 : ({ pt := X.pt, π := X.π ≫ 𝟙 F } =  X) = (({ pt := X.pt, π := X.π }) = X) := congrArg nat_gives_coneX comp_id -- equality of two t-nats leads to equality of the statement about those two t-nats
  exact t1 ▸ (eq_self X : (X = X) = True ) ▸ trivial -- we can prove the second statement easily, so the statement on the first t-nat is true. it is true when the original proposition is true.

-- much more direct
def a_niceproof_explicit2 (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=
  congrArg (fun α ↦ ({ pt := X.pt, π := α } : Cone F)) (Category.comp_id X.π)


@[simp]
theorem Cones.hom_eqToHom {F : J ⥤ M} {X Y : Cone F} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg Cone.pt h) := by cases h; simp

def coneFunctor : (J ⥤ M) ⥤ Cat where
  obj F := Cat.of (Cone F)
  map f := Cones.postcompose f
  map_id F := by
    dsimp
    have : Cones.postcompose (𝟙 F) = 𝟙 (Cat.of (Cone F)) := by
      fapply CategoryTheory.Functor.ext
      · have : ∀ (X : Cone F), (Cones.postcompose (𝟙 F)).obj X = (𝟭 (Cat.of (Cone F))).obj X := by
          intro X
          simp [Cones.postcompose]
        exact this
      · have : ∀ X Y f, (Cones.postcompose (𝟙 F)).map f = eqToHom (a_niceproof1 F X) ≫ (𝟭 (Cat.of (Cone F))).map f ≫ eqToHom (a_niceproof_explicit2 F Y).symm := by
          intro X Y f
          ext
          simp only [postcompose_map_hom ]
          simp only [Functor.id_map]
          simp only [Cone.category_comp_hom, ]
          simp only [Cones.hom_eqToHom, ]
          simp only [ eqToHom_refl, ]
          simp only [Category.comp_id, Category.id_comp]
        exact this
    exact this
  map_comp f g := by
    dsimp
    fapply CategoryTheory.Functor.ext
    · intro X
      simp [Cones.postcompose]
    · intro X Y f
      ext
      simp only [ postcompose_map_hom]
      simp only [ Cat.comp_obj,  Cat.comp_map]
      simp only [ Cone.category_comp_hom]
      simp only [ Cones.hom_eqToHom]
      simp only [ eqToHom_refl]
      simp only [ Category.comp_id, Category.id_comp]
      simp only [ postcompose_map_hom]
      --simp only [  Cat.comp_obj,  Cat.comp_map, Cone.category_comp_hom, Cones.hom_eqToHom, eqToHom_refl, Category.comp_id, Category.id_comp]
