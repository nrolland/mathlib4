import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
open CategoryTheory

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₂ } [Category.{v₂} C]
variable {x y : C}

def funfunfun (inv : C ⥤ B) (hom : B ⥤ C) (e :  𝟭 C = (inv ⋙ hom ) )
    (m m' : x ⟶ y) (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) :
    m = m' :=
  have as2 : HEq m ((inv ⋙ hom).map m) := Functor.hcongr_hom e m
  have as3 : HEq ((inv ⋙ hom).map m) ((inv ⋙ hom).map m') := heq_of_eq h
  have as4 : HEq ((inv ⋙ hom).map m') m' := (Functor.hcongr_hom e m').symm
  have as : HEq m m' := as2.trans (as3.trans  as4)
  eq_of_heq as


def funfunfunUsingEqToHom (inv : C ⥤ B) (hom : B ⥤ C) (e :  𝟭 C = (inv ⋙ hom ) )
    (m m' : x ⟶ y) (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) :
    m = m' :=
  have h₁ : m = eqToHom _ ≫ (inv ⋙ hom).map m ≫ eqToHom _ := Functor.congr_hom e m
  have h₂ : m' = eqToHom _ ≫ (inv ⋙ hom).map m' ≫ eqToHom _ := Functor.congr_hom e m'
  have qeqe : eqToHom _ ≫ (inv ⋙ hom).map m ≫ eqToHom _ = m' := (h ▸ h₂.symm)

  h₁.trans (h ▸ h₂.symm)
