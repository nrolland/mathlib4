import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Category.Cat
open CategoryTheory Limits

variable {J M : Type*} [Category J] [Category M]
set_option linter.style.longLine false
set_option linter.docPrime false

-- simp is a very powerful mechanism
def aniceproof0 (F : J ⥤ M) (X : Cone F) :  (Cones.postcompose (𝟙 F)).obj X =  X :=  by
      simp [Cones.postcompose]

-- lets break that down a bit, and clean some magic
def aniceproof1 (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=  by
      simp

-- now we can explicit the operations
def aniceproof_explicit (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=  by -- we want to prove a proposition on two cones
  let nat_gives_coneX : ((Functor.const J).obj X.pt ⟶ F) → Prop := fun α ↦ { pt := X.pt, π := α } = X -- we view the desired proposition on two cones as a statement on a single t-nat
  let comp_id : X.π ≫ 𝟙 F = X.π := Category.comp_id X.π -- we have equality of t-nat which is super strong statement
  let t1 : ({ pt := X.pt, π := X.π ≫ 𝟙 F } =  X) = (({ pt := X.pt, π := X.π }) = X) := congrArg nat_gives_coneX comp_id -- equality of two t-nats leads to equality of the statement about those two t-nats
  exact t1 ▸ (eq_self X : (X = X) = True ) ▸ trivial -- we can prove the second statement easily, so the statement on the first t-nat is true. it is true when the original proposition is true.

-- much more direct
def aniceproof_explicit2 (F : J ⥤ M) (X : Cone F) : { pt := X.pt, π := X.π ≫ 𝟙 F } =  X :=
  congrArg (fun α ↦ ({ pt := X.pt, π := α } : Cone F)) (Category.comp_id X.π)


-- @[simp]
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
      · --have : ∀ X Y f, (Cones.postcompose (𝟙 F)).map f = eqToHom (h_obj X) ≫ (𝟭 (Cat.of (Cone F))).map f ≫ eqToHom (h_obj Y).symm := by
          intro X Y f
          ext
          simp
          sorry
        --exact this
    exact this
  map_comp f g := by
    dsimp
    fapply CategoryTheory.Functor.ext
    · intro X
      simp [Cones.postcompose]
    · intro X Y f
      ext
      simp
      sorry
