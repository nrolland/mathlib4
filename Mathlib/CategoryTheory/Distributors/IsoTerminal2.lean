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
  functor_unitIso_comp := by
    intro c
    have := eqToHom_map i.hom (congrArg (fun f ↦ f.obj c)  i.hom_inv_id.symm)
    simp_all only [Functor.id_obj, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl]

noncomputable def isoOfCategoryIsoTerminalObj (i: IsoOfCategory B C)  (th : Terminal B ) :
  Terminal C :=
    let as : IsTerminal (i.hom.obj th.fst) := IsTerminal.isTerminalObj (equivOfIso i).functor th.fst th.snd
    ⟨i.hom.obj th.fst, as⟩


variable (E : C ≌ D)

-- set_option trace.Meta.synthInstance true

noncomputable example : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) E.functor :=
  inferInstance


noncomputable example : E.functor.IsEquivalence :=
  inferInstance


noncomputable example : E.functor.IsRightAdjoint :=
  inferInstance

def isRightAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsRightAdjoint F := F.asEquivalence.isRightAdjoint_functor


------
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

--- Comment l'enfer des types dependants est évité ?

--- Cette propriete ne l'évite pas
def rightAdjointPreservesLimits : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape := fun {J} =>
    { preservesLimit := fun {K : J ⥤ D} =>
        { preserves := fun {c} {hc : IsLimit c} => -- IsLimit (G.mapCone c)
            IsLimit.isoUniqueConeMorphism.inv fun (s : Cone (K ⋙ G)) =>
              let homequiv : (s ⟶ G.mapCone c) ≃ _ :=  ((adj.functorialityAdjunction' K).homEquiv s c).symm
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _) homequiv } }
--protected def Equiv.unique _ _ [Unique β] (e : α ≃ β) : Unique α
--def isoUniqueConeMorphism {t : Cone F} : IsLimit t ≅ ∀ s, Unique (s ⟶ t) where




---- enfer des types dependants


def isoOfCategoryIsoTerminalObjEnfer (x: B) (equiv:  B ≌ C)  (h : IsTerminal x  ) : IsTerminal (equiv.functor.obj x) :=

  -- the categories of cones are the same
  let coneCatquiv : Cone (Functor.empty B) ≌ Cone (empty B ⋙ equiv.functor) :=
    Limits.Cones.functorialityEquivalence (Functor.empty B) equiv

  -- "the" cone for the empty functor
  let theConeB : Cone (empty B) := asEmptyCone x

  -- IsLimit for theConeB is in bijection with IsLimit for "a" cone in C
  let qe : IsLimit (coneCatquiv.functor.obj theConeB) ≃ IsLimit theConeB  := IsLimit.ofConeEquiv coneCatquiv
  let aconeC_isLimit : IsLimit (coneCatquiv.functor.obj theConeB : Cone (empty B ⋙ equiv.functor))  := qe.invFun h

  ---------
  -- We want to rewrite that previous term thanks to an equality between "a" cone and "the" cone
  -- they are not of the same type
  let aconeC : Cone (empty B ⋙ equiv.functor) := coneCatquiv.functor.obj theConeB
  let theconeC : Cone (empty C) := asEmptyCone (equiv.functor.obj x)
  -- best we can hope is HEq
  let the_a_HEq : HEq theconeC aconeC := by sorry
  -- and we have some type identity
  let eqConeType : Cone (empty.{0} B ⋙ equiv.functor) = Cone (empty C) := congrArg Cone (empty_ext' _ _)

  let result : IsLimit (asEmptyCone (equiv.functor.obj x)) := by
    sorry
  result

def emptyConeExt {a b : Cone (empty C)} (h : a.pt = b.pt) : a ≅ b :=
  Cones.ext (eqToIso h) (fun a => a.as.elim)

def isoOfCategoryIsoTerminalObj' (x: B) (equiv:  B ≌ C) (h : IsTerminal x) : IsTerminal (equiv.functor.obj x) :=
  let coneCatequiv := (Cones.functorialityEquivalence _ equiv).trans
    (Cones.postcomposeEquivalence (emptyExt _ _))

  let equiv : coneCatequiv.functor.obj (asEmptyCone x) ≅ asEmptyCone (equiv.functor.obj x) :=
    emptyConeExt rfl

  ((IsLimit.ofConeEquiv coneCatequiv).invFun h).ofIsoLimit equiv


-- def isoOfCategoryIsoTerminalObjEnfer3 (x: B) (equiv:  B ≌ C) (h : IsTerminal x) : IsTerminal (equiv.functor.obj x) :=
--   let coneCatquiv :  (empty.{0} B) ≅  (empty.{0} C) :=  sorry

--   sorry
