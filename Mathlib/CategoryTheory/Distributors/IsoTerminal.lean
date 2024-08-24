import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso
import Mathlib.CategoryTheory.Distributors.EqToHomD
import Mathlib.CategoryTheory.Distributors.TerminalD
import Mathlib.CategoryTheory.Distributors.LimitGroupoid

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁ } [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₂ } [Category.{v₂} C]

variable (F G : J ⥤ B)

def toNewTerminal {i:  IsoOfCategory B C} {t : B} (h : IsTerminal t)  x :=
  have p : x = i.hom.obj (i.inv.obj x) := (hom_inv_idobj i x).symm
  eqToHom p ≫ i.hom.map (h.from (i.inv.obj x))


def isoOfCategoryIsoTerminal  (i:  IsoOfCategory B C)  :  Terminal B ⥤ Terminal C where
  obj := fun ⟨t,h⟩ =>
    ⟨i.hom.obj t,
      IsTerminal.ofUniqueHom
      (fun x =>
        let eqtohom := x |> hom_inv_idobj i |> Eq.symm |> eqToHom
        eqtohom ≫ i.hom.map (h.from (i.inv.obj x )))
      (fun x (m : x ⟶ i.hom.obj t) => -- on veut : m = toNewTerminal h x, dans C
        let q : i.inv.obj (i.hom.obj t) = t  :=  inv_hom_idobj i t

        -- on a :  (hom ⋙ inv).map m = (hom ⋙ inv).map (toNewTerminal h x), dans B
        have eq : i.hom.map (i.inv.map m ≫  eqToHom q) =
          i.hom.map (i.inv.map (toNewTerminal h x) ≫ eqToHom q)
          := congrArg i.hom.map (uniq_morphism_to_terminal h)

        have eq : i.hom.map (i.inv.map m ) =
          i.hom.map (i.inv.map (toNewTerminal h x) ≫ eqToHom q ≫  eqToHom q.symm) :=
            let wrg := (comp_eqToHom_iffMap i.hom q (i.inv.map m)
                        (i.inv.map (toNewTerminal h x) ≫ eqToHom q)).mp eq
            by rw [Category.assoc] at wrg
               exact wrg

        have eq : (i.inv ⋙ i.hom).map m  =
          (i.inv ⋙ i.hom).map (toNewTerminal h x) := by
          simp_all only [eq,Functor.map_comp, eqToHom_trans, eqToHom_refl,
          Category.comp_id, Functor.comp_map]

        idFunctorMap i.inv_hom_id  m (toNewTerminal h x) eq)
      ⟩
  map := sorry


def isoCatIsoTerminal (i: IsoOfCategory B C) : IsoOfCategory (Terminal B) (Terminal C) where
  hom := isoOfCategoryIsoTerminal i
  inv := isoOfCategoryIsoTerminal i.symm
  hom_inv_id := sorry
  inv_hom_id := sorry

def isoCatIsoTerminal2 (i: Cat.of B ≅ Cat.of C)  : Cat.of (Terminal B) ≅ Cat.of (Terminal C) :=
  -- have asdd  := isoFunctorIsoLimit (asEmptyConeIso i)
  sorry -- using

-- def isoFunctorIsoLimit {F G : J ⥤ B} (i: F ≅ G)  : Cat.of (Limit F) ≅ Cat.of (Limit G) :=
