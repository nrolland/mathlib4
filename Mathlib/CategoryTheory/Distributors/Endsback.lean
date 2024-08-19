import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering

open CategoryTheory

universe v₁ v₂ vm u₁ u₂ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {A : Type u₂ } [Category.{v₂} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]

variable (F : (Bᵒᵖ×B) ⥤ M)


def qweqw (einv : B ⥤ A) : A ⥤ M ≌ B ⥤ M :=
    whiskeringLeft.obj einv


def functor_cat_equiv (e : A ≌ B) : A ⥤ M ≌ B ⥤ M where
  functor := whiskeringLeft.obj e.inverse
  inverse := whiskeringLeft.obj e.functor

structure Wedge : Type (max (max um u₂) vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj (Opposite.op c,c)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (Opposite.op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (Opposite.op c, c')) := by aesop_cat

structure WedgeMorphism (x y : Wedge F) where
  Hom : x.pt ⟶ y.pt
  fac : ∀ (c : B),
    Hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.fac

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism _ x y
  id := fun x => {  Hom := 𝟙 x.pt }
  comp := fun f g =>  { Hom := f.Hom ≫ g.Hom}

--- practice around limits ---
set_option linter.longLine false
structure IsTerminalSimple (t : B) where
  lift : ∀ s : B, s ⟶ t
  uniq : ∀ (s : B) (m : s ⟶ t), m = lift s := by aesop_cat
def IsTerminalUnique (t:B) := ∀ X : B, Unique (X ⟶ t)
def equiv1 (t:B) : (IsTerminalSimple t) ≅ IsTerminalUnique t where
  hom (ts) x := { default := ts.lift x, uniq := ts.uniq x}
  inv w := { lift := fun s => (w s).default, uniq := fun s => (w s).uniq}
def equiv2 (t : B) : (IsTerminalSimple t) ≅ Limits.IsLimit (Limits.asEmptyCone t ) where
  hom w :=  Limits.IsTerminal.ofUniqueHom (w.lift) (w.uniq)
  inv w := { lift := fun s =>  w.lift (Limits.asEmptyCone s)
             uniq :=  fun s m => w.uniq (Limits.asEmptyCone s) m (fun ⟨j⟩ => j.elim) }

def from_wedge_to_cone (w : Wedge F) : Limits.Cone (CategoryOfElements.π (Functor.hom B) ⋙ F ) := {
  pt := w.pt
  π := {
    app  := fun (⟨(bo,b'),f⟩) => w.leg bo.unop ≫ F.map (𝟙 bo, f)
    naturality := fun (⟨(bop,b'),f⟩) (⟨(cop,c'),g⟩)
      (⟨((uo : bop ⟶ cop), (v : b' ⟶ c') ),h⟩)  => by
        dsimp at uo v h
        let b := bop.unop
        let c := cop.unop
        change b ⟶ b' at f
        change c ⟶ c' at  g
        change  uo.unop ≫ f ≫ v = g at h

        simp
        have : w.leg c ≫ F.map (𝟙 cop, g) = w.leg b ≫ (F.map (𝟙 bop, f)) ≫ (F.map ((uo, v) : (bop, b') ⟶ (cop,c') )):= by
          rw [<- h]
          have : (𝟙 cop = 𝟙 cop ≫ 𝟙 cop ≫ 𝟙 cop) := by aesop_cat
          rw [this]
          rw [← prod_comp _ _ ((𝟙 cop, uo.unop))  ((𝟙 cop ≫ 𝟙 cop , f ≫ v))]
          rw [← prod_comp _ _ ((𝟙 cop, f))  ((𝟙 cop, v))]
          rw [F.map_comp, F.map_comp]
          rw [<- Category.assoc]
          rw [<-op_id, w.wedgeCondition uo.unop]
          rw [Category.assoc, ← F.map_comp,← F.map_comp,← F.map_comp]
          simp_all only [Opposite.op_unop, Quiver.Hom.op_unop, prod_comp, op_id, Category.comp_id, Category.id_comp]

        exact this
        }
}



-- missing : a wedge for F is a cone for F . pi
-- missing : un wedge pour F est un cone pour F . p
-- missing : un terminal wedge pour F est terminal cone pour F . p -- terminal + iso
-- missing Nat(F,G) ≅ end B(F-,G=)



---



/-- end is a terminal wedges -/
noncomputable def end_summit [Limits.HasTerminal (Wedge F)] := Limits.terminal (Wedge F)

def endCone [Limits.HasLimit ((CategoryOfElements.π (Functor.hom B)) ⋙ F)] : Type _ :=
  Limits.LimitCone ((CategoryOfElements.π (Functor.hom B)) ⋙ F)


#min_imports
