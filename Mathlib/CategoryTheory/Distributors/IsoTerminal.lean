import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Distributors.TerminalD
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib
set_option linter.longLine false

open CategoryTheory
open Limits
open IsLimit
open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v vm u₁ u₂ u₃ u₄ u um w
variable {J : Type u₁ } [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {D : Type u₄ } [Category.{v₄} D]

variable (F G : J ⥤ B)

def equivOfIso (i: IsoOfCategory C D)  : C ≌ D where
  functor := i.hom
  inverse := i.inv
  unitIso :=  eqToIso i.hom_inv_id.symm
  counitIso := eqToIso i.inv_hom_id
  functor_unitIso_comp := fun c =>  by
    have := eqToHom_map i.hom (congrArg (fun f ↦ f.obj c)  i.hom_inv_id.symm)
    simp_all only [Functor.id_obj, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl]

noncomputable def isoOfCategoryIsoTerminalObj' (i: IsoOfCategory B C)  (th : Terminal B ) :
  Terminal C := ⟨i.hom.obj th.fst, IsTerminal.isTerminalObj (equivOfIso i).functor th.fst th.snd⟩

private def isoOfCategoryIsoTerminalObj (i: IsoOfCategory B C) (th : Terminal B) : Terminal C :=
  let coneCatequiv := (Cones.functorialityEquivalence _ (equivOfIso i)).trans
    (Cones.postcomposeEquivalence (emptyExt _ _))
  ⟨i.hom.obj th.fst, ((IsLimit.ofConeEquiv coneCatequiv).invFun th.snd).ofIsoLimit (emptyConeExt rfl)⟩

def isoOfCategoryIsoTerminal (i:  IsoOfCategory B C) : Terminal B ⥤ Terminal C where
  obj := isoOfCategoryIsoTerminalObj i
  map f := i.hom.map f
  map_id  tx := uniq_morphism_to_terminal (isoOfCategoryIsoTerminalObj i tx).snd
  map_comp {_ _ tz} _ _ := uniq_morphism_to_terminal (isoOfCategoryIsoTerminalObj i tz).snd

theorem isoOfCategory_IsoTerminal_comp (i:  IsoOfCategory B C ) (j:  IsoOfCategory C D) :
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
