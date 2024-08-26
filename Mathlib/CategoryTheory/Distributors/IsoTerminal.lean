import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Distributors.TerminalD
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ v₄ vm u₁ u₂ u₃ u₄ u um
variable {J : Type u₁ } [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {D : Type u₄ } [Category.{v₄} D]

variable (F G : J ⥤ B)

def toNewTerminal {i:  IsoOfCategory B C} {t : B} (h : IsTerminal t)  x :=
  have p : x = i.hom.obj (i.inv.obj x) := (hom_inv_idobj i x).symm
  eqToHom p ≫ i.hom.map (h.from (i.inv.obj x))

def isoOfCategoryIsoTerminalObj  (i: IsoOfCategory B C)  (th : Terminal B ) : Terminal C :=
let t:= th.fst; let h := th.snd
let toNewTerminal {i:  IsoOfCategory B C} {t : B} (h : IsTerminal t)  x :=
  have p : x = i.hom.obj (i.inv.obj x) := (hom_inv_idobj i x).symm
  eqToHom p ≫ i.hom.map (h.from (i.inv.obj x))
⟨i.hom.obj t,
  IsTerminal.ofUniqueHom
  (fun x =>
    let eqtohom := x |> hom_inv_idobj i |> Eq.symm |> eqToHom
    eqtohom ≫ i.hom.map (h.from (i.inv.obj x )))
  (fun x (m : x ⟶ i.hom.obj t) => -- on veut : m = toNewTerminal h x, dans C
    let q : i.inv.obj (i.hom.obj t) = t  :=  inv_hom_idobj i t

    have eq : i.hom.map (i.inv.map m ≫  eqToHom q) =
      i.hom.map (i.inv.map (toNewTerminal h x) ≫ eqToHom q)
      := congrArg i.hom.map (uniq_morphism_to_terminal (h))

    have eq : i.hom.map (i.inv.map m ) =
      i.hom.map (i.inv.map (toNewTerminal (h) x) ≫ eqToHom q ≫  eqToHom q.symm) :=
        let wrg := (comp_eqToHom_iffMap i.hom q (i.inv.map m)
                    (i.inv.map (toNewTerminal h x) ≫ eqToHom q)).mp eq
        by rw [<- Category.assoc]; exact wrg

    have eq : (i.inv ⋙ i.hom).map m  =
      (i.inv ⋙ i.hom).map (toNewTerminal (h) x) := by
      simp_all only [eq,Functor.map_comp, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Functor.comp_map]
    idFunctorMap i.inv_hom_id  m (toNewTerminal (h) x) eq)⟩


def equivOfIso (i: IsoOfCategory C D)  : C ≌ D where
  functor := i.hom
  inverse := i.inv
  unitIso :=  eqToIso i.hom_inv_id.symm
  counitIso := eqToIso i.inv_hom_id
  functor_unitIso_comp := by
    intro c
    have := eqToHom_map i.hom (congrArg (fun f ↦ f.obj c)  i.hom_inv_id.symm)
    simp_all only [Functor.id_obj, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl]

noncomputable def isoOfCategoryIsoTerminalObj' (i: IsoOfCategory B C)  (th : Terminal B ) :
  Terminal C :=
    ⟨i.hom.obj th.fst, IsTerminal.isTerminalObj (equivOfIso i).functor th.fst th.snd⟩



def isoOfCategoryIsoTerminal (i:  IsoOfCategory B C) : Terminal B ⥤ Terminal C where
  obj := isoOfCategoryIsoTerminalObj i
  map f := i.hom.map f
  map_id  tx := uniq_morphism_to_terminal (isoOfCategoryIsoTerminalObj i tx).snd
  map_comp {_ _ tz} _ _ := uniq_morphism_to_terminal (isoOfCategoryIsoTerminalObj i tz).snd

lemma isoOfCategory_IsoTerminal_comp (i:  IsoOfCategory B C ) (j:  IsoOfCategory C D) :
    (isoOfCategoryIsoTerminal i) ⋙ (isoOfCategoryIsoTerminal j) =
      ( isoOfCategoryIsoTerminal (i.trans j))
 := Functor.hext
    fun x => by
      simp_all only [Functor.comp_obj]
      ext1
      · rfl
      · simp_all only [heq_eq_eq]
        apply Subsingleton.elim
    fun X Y f => by
        simp_all only [Functor.comp_obj, Functor.comp_map, heq_eq_eq]
        rfl

def isoCatIsoTerminal (i: IsoOfCategory B C) : IsoOfCategory (Terminal B) (Terminal C) where
  hom := isoOfCategoryIsoTerminal i
  inv := isoOfCategoryIsoTerminal i.symm
  hom_inv_id := by
    rw [isoOfCategory_IsoTerminal_comp, comp_symm_id]
    apply Functor.hext
    · intro th
      dsimp
      ext1
      · rfl
      · simp_all only [heq_eq_eq]
        apply Subsingleton.elim
    · intro _ _ _
      simp_all only [Functor.id_obj, Functor.id_map, heq_eq_eq]
      rfl
  inv_hom_id := by
    rw [isoOfCategory_IsoTerminal_comp, symm_comp_id]
    apply Functor.hext
    · intro th
      dsimp
      ext1
      · rfl
      · simp_all only [heq_eq_eq]
        apply Subsingleton.elim
    · intro _ _ _
      simp_all only [Functor.id_obj, Functor.id_map, heq_eq_eq]
      rfl
