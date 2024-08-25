import Mathlib.CategoryTheory.EqToHom

open CategoryTheory

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]

variable (F  : J ⥤ B)

theorem comp_eqToHom_iffMap {x y y'  : J} (p : y = y') (f : x ⟶ y) (g : x ⟶ y') :
 ( F.map (f ≫ eqToHom p) = F.map g ) ↔ (F.map f = F.map (g ≫ eqToHom p.symm)) :=
    let other := (comp_eqToHom_iff (congrArg F.obj p) (F.map f) (F.map g))
    { mp := fun h => by
        rw [F.map_comp, eqToHom_map F p] at h
        have q := other.mp h ;
        rw [F.map_comp, eqToHom_map F p.symm]
        exact q
      mpr := fun h => by
        rw [F.map_comp, eqToHom_map F p.symm] at h
        have q := other.mpr h ;
        rw [F.map_comp, eqToHom_map F p]
        exact q }
