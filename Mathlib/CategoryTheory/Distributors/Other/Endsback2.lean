import Mathlib.CategoryTheory.Equivalence

open CategoryTheory

universe v₁ v₂ vm u₁ u₂ u um
variable {A : Type u₂ } [Category.{v₂} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]


def functor_cat_equiv (e : A ≌ B) : A ⥤ M ≌ B ⥤ M where
  functor := (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := sorry
  counitIso := sorry
