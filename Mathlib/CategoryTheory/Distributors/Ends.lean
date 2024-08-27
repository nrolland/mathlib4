import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Distributors.LimitGroupoid
import Mathlib.CategoryTheory.Distributors.IsoTerminal
/-!
# Wedges and Ends

-- les lemmes sont typiquement + simple avec les cones, pour lesquel ils existent deja

-/
namespace CategoryTheory

open CategoryTheory
open CategoryOfElements
open Functor
open Opposite

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)
set_option linter.longLine false
infixr:90 " ⋗ " => fun f g ↦ Function.comp g f

section Wedge
@[ext]
structure Wedge : Type (max (max um u₂) vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj (op c,c)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (op c, c')) := by aesop_cat

@[ext]
structure WedgeMorphism  {F : (Bᵒᵖ×B) ⥤ M} (x y : Wedge F) where
  hom : x.pt ⟶ y.pt
  fac : ∀ (c : B), hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.fac

instance : Category (Wedge F) where
  Hom x y:=  WedgeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := {
    hom := f.hom ≫ g.hom
    fac := fun c => by
      simp_all only [Category.assoc, WedgeMorphism.fac] }

-- typiquement + simple avec les cone, pour lesquel il existe bcp de lemmes
def wedgeHom {F G : (Bᵒᵖ×B) ⥤ M} (α : F ⟶ G) : Wedge F ⥤ Wedge G  where
  obj w :=  {
    pt := w.pt
    leg := fun c =>  w.leg c ≫ α.app (op c, c)
    wedgeCondition := fun a b f => by
          dsimp
          rw [Category.assoc, <- α.naturality ((𝟙 (op a), f) : (op a, a) ⟶ (op a, b))]
          rw [Category.assoc, <- α.naturality ((f.op, 𝟙 b) : (op b, b) ⟶ (op a, b))]
          have : (𝟙 a).op = 𝟙 (op a) := rfl
          rw [<- this]
          rw [<- Category.assoc, w.wedgeCondition f, Category.assoc] }
  map {X Y} m := {
    hom := m.hom
    fac := fun c => by dsimp;rw [<-  m.fac c, Category.assoc ] }

def isoFctrIsoWedge' {F G : (Bᵒᵖ×B) ⥤ M} (i: F ≅ G) : Wedge F ≅ Wedge G  where
  hom := (wedgeHom i.hom).obj
  inv := (wedgeHom i.inv).obj
  hom_inv_id : (wedgeHom i.hom).obj ≫ (wedgeHom i.inv).obj = 𝟙 (Wedge F) := by
    funext x
    apply Wedge.ext;rfl
    · apply heq_iff_eq.mpr
      dsimp
      funext c
      have : ((wedgeHom i.inv).obj ((wedgeHom i.hom).obj x)).leg c =  (x.leg c ≫ i.hom.app (op c, c)) ≫  i.inv.app (op c, c) := rfl
      simp_all only [Iso.hom_inv_id_app, Category.comp_id, Category.assoc]
  inv_hom_id := by
    funext x
    apply Wedge.ext;rfl
    · apply heq_iff_eq.mpr
      dsimp
      funext c
      have : ((wedgeHom i.hom).obj ((wedgeHom i.inv).obj x)).leg c =  (x.leg c ≫ i.inv.app (op c, c)) ≫  i.hom.app (op c, c) := rfl
      simp_all only [Iso.inv_hom_id_app, Category.comp_id, Category.assoc]


def isoFctrIsoWedge {F G : (Bᵒᵖ×B) ⥤ M} (i: F ≅ G) : IsoOfCategory (Wedge F)  (Wedge G)  where
  hom := sorry --  : B ⥤ C
  inv := sorry -- : C ⥤ B
  hom_inv_id := sorry --  : hom ⋙ inv = 𝟭 B := by aesop_cat
  inv_hom_id := sorry -- : inv ⋙ hom = 𝟭 C := by aesop_cat

end Wedge


section Ends

/-- An end is a terminal wedge -/
abbrev Ends :=  Terminal (Wedge F)

/-- ends forms a groupoid -/
instance endGroupoid : Groupoid (Ends F) := terminalGroupoid
def connected (x y : Ends F) : x ⟶ y := y.2.from x.1
def Ends.uniqueUpToIso {T T' : C} (th : Terminal (Wedge F)) (th' : Terminal (Wedge F)) : th.fst ≅ th'.fst := sorry -- pas necessaire


-- TODO : comme composition de isoFctrIsoWedge et isoCatIsoTerminal.obj
def isoFctrIsoIsTerminalWedge {G : (Bᵒᵖ×B) ⥤ M} (i: F ≅ G) (x : Wedge F) : (Limits.IsTerminal x) ≅ (Limits.IsTerminal ((isoFctrIsoWedge i).hom.obj x)) :=  sorry

-- TODO : comme composition de isoFctrIsoWedge et isoCatIsoTerminal
def isoFctrIsoEndDirect (G : (Bᵒᵖ×B) ⥤ M) (i: F ≅ G)  : IsoOfCategory (Ends F) (Ends G)  := sorry

-- Plus tard : on passe par Cat
def isoFctrIsoEnd1 {G : (Bᵒᵖ×B) ⥤ M} (i:  F ≅ G)  : Cat.of (Wedge F) ≅ Cat.of (Wedge G) :=  sorry


------------------------------------------------------------------------------------------------
variable {A : Type v₂ } [Category.{v₁} A]

def natAsWedge (F G : A ⥤ B): Wedge ( F.op.prod G ⋙ hom B)  where
  pt := NatTrans F G
  leg a α := α.app a
  wedgeCondition _ _ _ := funext (fun _ => by simp)

def natAsWedge2 (F G : A ⥤ B): Wedge ( F.op.prod G ⋙ hom B) :=
  Wedge.mk (NatTrans F G) (fun a α ↦ α.app a) fun _ _ _ => funext (fun _ => by simp)


def natAsWedgeIsTerminal (F G : A ⥤ B) : Limits.IsTerminal (natAsWedge F G ) :=
  Limits.IsTerminal.ofUniqueHom (fun W => {
    hom := fun x : W.pt => {
      app := fun a => W.leg a x
      naturality := fun a b f => by
        let h := congrFun ((W.wedgeCondition f).symm) x
        simp at (h);
        exact h}
    fac := fun _ => funext fun _ => rfl
  })
  (fun X m => by
    apply WedgeMorphism.ext
    funext x
    apply NatTrans.ext
    ext a
    exact ( congrFun (m.fac a) x))


def natAsEnd (F G : A ⥤ B): Ends ( F.op.prod G ⋙ hom B) := ⟨natAsWedge F G, natAsWedgeIsTerminal F G⟩

def toEnd (F G : A ⥤ B) (α : NatTrans F G) : (natAsEnd F G).1.pt := α

----

-- advanced
-- "Nat(F,G)  ≃: End B(F-,G=)"  := (CC (End B(F-,G=))).mk (defaultEnd (Nat(F,G)))
-- "xpt : M ≃: Terminal C"   := (CC (Terminal C)).mk (defaultC x : C, isTerminal (defaultC x))

-- basic
-- "(natAsWedge F G, natAsEnd F G) ≃: End B(F-,G=)" = (CC (End B(F-,G=))).mk (natAsWedge F G, natAsEnd F G)
-- "(x : C, IsTerminal x)" ≃: Terminal C  := (CC (Terminal C)).mk (x : C, IsTerminal x)

-- def (≃:) (x : C, IsTerminal x)  :=
-- protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=  Quot.mk Setoid.r a




-- Pour notre affaire :

-- B(F-,G=) : bop * b -> set
-- [Bop,Set](B( , F-), B( , G=)) : bop * b -> set
-- iso

-- categorie de wedge pour  B(F-,G=)
-- categorie de wedge pour l'autre
-- iso

-- terminal pour l'un
-- terminal pour l'autre
-- iso


------------------------------------------------------------------------------------------------
end Ends

section wedgeandcone
-- def end_ascone_aswedge_equiv [Limits.HasLimit ((CategoryOfElements.π (hom B)) ⋙ F)]
--     [Limits.HasTerminal (Wedge F)]: endAsCone F ≅ endAsWedge F  := sorry
end wedgeandcone
