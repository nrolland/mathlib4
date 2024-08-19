import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category

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
  fac : ∀ (c : B),
    hom ≫ y.leg c = x.leg c := by aesop_cat

attribute [simp] WedgeMorphism.fac

instance : Category (Wedge F) where
  Hom := fun x y => WedgeMorphism x y
  id := fun x => { hom := 𝟙 x.pt }
  comp := fun f g =>  { hom := f.hom ≫ g.hom }

abbrev End :=  Σ x : Wedge F, Limits.IsTerminal x

def wr {a b : B} {c d : C} (fg : (a ⟶ b) × (c ⟶ d)) : (a,c) ⟶ (b,d):= (fg.1,fg.2)

def isoWedgeFromFctrHom (G : (Bᵒᵖ×B) ⥤ M) (i: F ⟶ G) : Wedge F ⥤ Wedge G  where
  obj w :=  {
    pt := w.pt
    leg := fun c =>  w.leg c ≫ i.app (op c, c)
    wedgeCondition := fun a b f => by
          dsimp
          rw [Category.assoc, <- i.naturality ((𝟙 (op a), f) : (op a, a) ⟶ (op a, b))]
          rw [Category.assoc, <- i.naturality ((f.op, 𝟙 b) : (op b, b) ⟶ (op a, b))]
          have : (𝟙 a).op = 𝟙 (op a) := rfl
          rw [<- this]
          rw [<- Category.assoc, w.wedgeCondition f, Category.assoc]
  }
  map {W Z} f := { hom := sorry, fac := sorry}

def isoWedgeFromFctrInv (G : (Bᵒᵖ×B) ⥤ M) (i: F ≅ G) : Wedge F ≅ Wedge G  where
  hom := sorry
  inv := sorry


def isoEndFromFctr (G : (Bᵒᵖ×B) ⥤ M) (i: F ≅ G)  (x : End F) : End G  :=
  match x with
  | ⟨xw,lx⟩ => sorry

/-- end is a terminal wedges -/
noncomputable def endWedge [Limits.HasTerminal (Wedge F)] := Limits.terminal (Wedge F)

------------------------------------------------------------------------------------------------
variable {A : Type v₂ } [Category.{v₁} A]

def natAsWedge (F G : A ⥤ B): Wedge ( F.op.prod G ⋙ hom B)  where
  pt := NatTrans F G
  leg a α := α.app a
  wedgeCondition a b f := funext (fun _ => by simp)

def natAsEnd (F G : A ⥤ B) : Limits.IsTerminal (natAsWedge F G ) :=
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


------------------------------------------------------------------------------------------------
section wedgeandcone
variable (F : (Bᵒᵖ×B) ⥤ M)


/-- A cone for `F . π ` is a wedge for `F` -/
def coneToWedge  : (Limits.Cone (π (hom B) ⋙ F)) ⥤ (Wedge F) where
  obj c :=  {
    leg  := fun (c': B) => c.π.app ⟨(op c',c'),𝟙 c'⟩
    wedgeCondition  := fun d d' f => by
      have sq2 := c.w (j := ⟨(op d, d), 𝟙 d⟩) (j' := ⟨(op d, d'), f⟩) ⟨(𝟙 _, f), by simp⟩
      have sq1 := c.w (j := ⟨(op d', d'), 𝟙 d'⟩) (j' := ⟨(op d, d'), f⟩) ⟨(f.op, 𝟙 _), by simp⟩
      dsimp at *; rw [sq1,sq2] }
  map f := { hom := f.hom }

/-- A wedge for `F` is a cone for `F . π ` -/
@[simp] def wedgeToCone (F : (Bᵒᵖ × B) ⥤ M) :  (Wedge F) ⥤ (Limits.Cone (π (hom B) ⋙ F)) where
  obj w := {
    π := {
      app  := fun (⟨(bo,b'),f⟩) => w.leg bo.unop ≫ F.map (𝟙 bo, f)
      naturality := fun (⟨(bop,b'),f⟩) (⟨(cop,c'),g⟩)
        (⟨((uo : bop ⟶ cop), (v : b' ⟶ c') ),h⟩)  => by
          dsimp at uo v h
          let b := bop.unop
          let c := cop.unop
          change b ⟶ b' at f
          change c ⟶ c' at g
          change uo.unop ≫ f ≫ v = g at h

          simp
          have : w.leg c ≫ F.map (𝟙 cop, g) =
            w.leg b ≫ (F.map (𝟙 bop, f)) ≫ (F.map ((uo, v) : (bop, b') ⟶ (cop,c') )):= by
            rw [<- h]
            have : (𝟙 cop = 𝟙 cop ≫ 𝟙 cop ≫ 𝟙 cop) := by aesop_cat
            rw [this]
            rw [← prod_comp _ _ ((𝟙 cop, uo.unop))  ((𝟙 cop ≫ 𝟙 cop , f ≫ v))]
            rw [← prod_comp _ _ ((𝟙 cop, f))  ((𝟙 cop, v))]
            rw [F.map_comp, F.map_comp]
            rw [<- Category.assoc]
            rw [<-op_id, w.wedgeCondition uo.unop]
            rw [Category.assoc, ← F.map_comp,← F.map_comp,← F.map_comp]
            simp_all only [Quiver.Hom.op_unop, prod_comp, op_id, Category.comp_id, Category.id_comp]
          exact this
          }
  }
  map f := {
    hom := f.hom
    w := fun (⟨(d,_),_⟩) => by dsimp; rw [← f.fac d.unop, Category.assoc] }

-- Equivalence of categories of Wedge(F) and Cone(π (hom B) ⋙ F)
def equivalence_ConeFbar_WedgeF : Equivalence (Wedge F) (Limits.Cone (π (hom B) ⋙ F)) where
  functor := wedgeToCone F
  inverse := coneToWedge F
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

def endAsCone [Limits.HasLimit ((CategoryOfElements.π (hom B)) ⋙ F)] : Type _ :=
  Limits.LimitCone ((CategoryOfElements.π (hom B)) ⋙ F)


-- missing : un terminal wedge pour F est terminal cone pour F . p -- terminal + iso

-- def end_ascone_aswedge_equiv [Limits.HasLimit ((CategoryOfElements.π (hom B)) ⋙ F)]
--     [Limits.HasTerminal (Wedge F)]: endAsCone F ≅ endAsWedge F  := sorry
end wedgeandcone
