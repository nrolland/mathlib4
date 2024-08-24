import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₂ } [Category.{v₂} C]

variable (F G : J ⥤ B)


def idFunctorMap {hom : B ⥤ C}{inv : C ⥤ B} (e : inv ⋙ hom = 𝟭 C)
  {x y : C}  (m m' : x ⟶ y)
  (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) : m = m' :=
    have h₁ :  m  = _ := Functor.congr_hom e.symm m
    have h₂ :  m' = _ := Functor.congr_hom e.symm m'
    h₁.trans (h ▸ h₂.symm)

theorem mapeq (F  : J ⥤ B) { y y'  : J} (p : y = y') : F.map (eqToHom p) =  eqToHom (congrArg F.obj p) :=
  by subst p;  simp_all only [eqToHom_refl, Functor.map_id]

theorem symeq (F  : J ⥤ B) { y y'  : J} (p : y = y') : (congrArg F.obj p).symm = congrArg F.obj p.symm :=
  by subst p; simp_all only


def asEmptyConeMorphism {x y : C} (f : x ⟶ y) :
    Limits.ConeMorphism (Limits.asEmptyCone x) (Limits.asEmptyCone y) :=
    { hom := f }

theorem uniq_morphism_to_terminal {s t : B} (h : IsTerminal t) {f f' : s ⟶ t} : f = f' :=
  congrArg ConeMorphism.hom (uniq_cone_morphism h : asEmptyConeMorphism f = asEmptyConeMorphism f')


def toNewTerminal {i:  IsoOfCategory B C} {t : B} (h : IsTerminal t)  x :=
  have p : x = i.hom.obj (i.inv.obj x) := (hom_inv_idobj i x).symm
  eqToHom p ≫ i.hom.map (h.from (i.inv.obj x))



theorem comp_eqToHom_iffMap {x y y'  : J} (p : y = y') (f : x ⟶ y) (g : x ⟶ y') :
 ( F.map (f ≫ eqToHom p) = F.map g ) ↔ (F.map f = F.map (g ≫ eqToHom p.symm)) :=
    let other := (comp_eqToHom_iff (congrArg F.obj p) (F.map f) (F.map g))
    { mp := fun h => by
        rw [F.map_comp, mapeq F p] at h
        have q := other.mp h ;
        rw [F.map_comp, mapeq F p.symm]
        exact q
      mpr := fun h => by
        rw [F.map_comp, mapeq F p.symm] at h
        have q := other.mpr h ;
        rw [F.map_comp, mapeq F p]
        exact q }


def isoOfCategoryIsoTerminal (i:  IsoOfCategory B C)
  (t : B) (h : IsTerminal t) : IsTerminal (i.hom.obj t) :=
  IsTerminal.ofUniqueHom (toNewTerminal h)
  (fun x (m : x ⟶ i.hom.obj t) => -- on veut : m = toNewTerminal h x, dans C

    let q : i.inv.obj (i.hom.obj t) = t  :=  inv_hom_idobj i t

    -- on a : inv m = inv (toNewTerminal h x), dans B
    have uniq : i.inv.map m ≫  eqToHom q = i.inv.map (toNewTerminal h x) ≫ eqToHom q
      := uniq_morphism_to_terminal h

    -- on a :  (hom ⋙ inv).map m = (hom ⋙ inv).map (toNewTerminal h x), dans B
    have eq : i.hom.map (i.inv.map m ≫  eqToHom q) =
      i.hom.map (i.inv.map (toNewTerminal h x) ≫ eqToHom q) := congrArg i.hom.map uniq


    have eq : i.hom.map (i.inv.map m ) =
      i.hom.map (i.inv.map (toNewTerminal h x) ≫ eqToHom q ≫  eqToHom q.symm) :=
        let wrg := (comp_eqToHom_iffMap i.hom q (i.inv.map m) (i.inv.map (toNewTerminal h x) ≫ eqToHom q)).mp eq
        by rw [Category.assoc] at wrg
           exact wrg

    have eq : i.hom.map (i.inv.map m ) =
      i.hom.map (i.inv.map (toNewTerminal h x)) := by
      simp only [eq,  eqToHom_trans, eqToHom_refl, Category.comp_id]

    have eq : (i.inv ⋙ i.hom).map m  =
      (i.inv ⋙ i.hom).map (toNewTerminal h x) := by
      simp_all only [eq,Functor.map_comp, eqToHom_trans, eqToHom_refl, Category.comp_id, Functor.comp_map]

    idFunctorMap i.inv_hom_id  m (toNewTerminal h x) eq    )
