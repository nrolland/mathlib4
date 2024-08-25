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

def isoOfCategoryIsoTerminalObj  (i: IsoOfCategory B C)  (th : Terminal B ) : Terminal C :=
    let ⟨t,h⟩  := th
    ⟨i.hom.obj th.fst,
      IsTerminal.ofUniqueHom
      (fun x =>
        let eqtohom := x |> hom_inv_idobj i |> Eq.symm |> eqToHom
        eqtohom ≫ i.hom.map ((th.snd).from (i.inv.obj x )))
      (fun x (m : x ⟶ i.hom.obj th.fst) => -- on veut : m = toNewTerminal h x, dans C
        let q : i.inv.obj (i.hom.obj th.fst) = th.fst  :=  inv_hom_idobj i th.fst

        have eq : i.hom.map (i.inv.map m ≫  eqToHom q) =
          i.hom.map (i.inv.map (toNewTerminal th.snd x) ≫ eqToHom q)
          := congrArg i.hom.map (uniq_morphism_to_terminal (th.snd))

        have eq : i.hom.map (i.inv.map m ) =
          i.hom.map (i.inv.map (toNewTerminal (th.snd) x) ≫ eqToHom q ≫  eqToHom q.symm) :=
            let wrg := (comp_eqToHom_iffMap i.hom q (i.inv.map m)
                        (i.inv.map (toNewTerminal th.snd x) ≫ eqToHom q)).mp eq
            by rw [Category.assoc] at wrg
               exact wrg

        have eq : (i.inv ⋙ i.hom).map m  =
          (i.inv ⋙ i.hom).map (toNewTerminal (th.snd) x) := by
          simp_all only [eq,Functor.map_comp, eqToHom_trans, eqToHom_refl,
          Category.comp_id, Functor.comp_map]

        idFunctorMap i.inv_hom_id  m (toNewTerminal (th.snd) x) eq)⟩

def isoOfCategoryIsoTerminal (i:  IsoOfCategory B C) : Terminal B ⥤ Terminal C where
  obj := isoOfCategoryIsoTerminalObj i
  map {x y} f := i.hom.map f
  map_id  := fun  th => -- map (𝟙 b) = 𝟙 (obj b) a faire
    by
      simp
      apply uniq_morphism_to_terminal
      let ⟨t', h'⟩ := isoOfCategoryIsoTerminalObj i th
      have : (isoOfCategoryIsoTerminalObj i th).fst = (i.hom.obj th.fst):= rfl
      exact (isoOfCategoryIsoTerminalObj i th).snd
  map_comp :=  -- map (f ≫ g) = map f ≫ map g
      sorry -- idem

abbrev Simple (B : Type u₂ ) [Category.{v₂} B] :=  Σ x : B, Bool

def simplObj  (i: B → C)  (th : Simple B ) : Simple C :=
    ⟨i th.fst, true⟩

def isoOK (i: B → C) ( th : Simple B) : True := by
      have : (i th.fst) = (simplObj i th).fst := rfl
      sorry

def isoKO (i: B → C)  ( th : Simple B) : True := by
      let ⟨t', h'⟩ := simplObj i th
      have : (i th.fst) =  t' := rfl
      sorry


def isoCatIsoTerminal (i: IsoOfCategory B C) : IsoOfCategory (Terminal B) (Terminal C) where
  hom := isoOfCategoryIsoTerminal i
  inv := isoOfCategoryIsoTerminal i.symm
  hom_inv_id := sorry -- a faire
  inv_hom_id := sorry

def isoCatIsoTerminal2 (i: Cat.of B ≅ Cat.of C)  : Cat.of (Terminal B) ≅ Cat.of (Terminal C) :=
  -- have asdd  := isoFunctorIsoLimit sorry
  sorry -- using

-- def isoFunctorIsoLimit {F G : J ⥤ B} (i: F ≅ G)  : Cat.of (Limit F) ≅ Cat.of (Limit G) :=
