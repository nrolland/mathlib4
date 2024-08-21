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
set_option linter.longLine false

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

theorem hext' {F G : B ⥤ C} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f

#check WedgeMorphism.ext


-- def hEqWedgeMorphism {x y a b : Wedge F} (f : WedgeMorphism x y) (g : WedgeMorphism a b)
--     (hxa : x.pt = a.pt ) (hyb : y.pt = b.pt ) (hh : f.hom = eqToHom hxa ≫ g.hom ≫ eqToHom hyb.symm):
--       HEq f g  :=
--       sorry

-- inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
--   | refl (a : α) : HEq a a




-- /-- Proving equality between functors. This isn't an extensionality lemma,
--   because usually you don't really want to do this. -/
-- theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
--     (h_map : ∀ X Y f,
--       F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by aesop_cat) :
--     F = G := by
--   match F, G with
--   | mk F_pre _ _ , mk G_pre _ _ =>
--     match F_pre, G_pre with  -- Porting note: did not unfold the Prefunctor unlike Lean3
--     | Prefunctor.mk F_obj _ , Prefunctor.mk G_obj _ =>
--     obtain rfl : F_obj = G_obj := by
--       ext X
--       apply h_obj
--     congr
--     funext X Y f
--     simpa using h_map X Y f

-- WedgeMorphism.ext : x_1.hom = y_1.hom → x_1 = y_1

-- /-- Proving equality between functors using heterogeneous equality. -/
-- theorem hext {X Y: Wedge F} (m n : WedgeMorphism X Y)
--     (h_map : HEq (m.hom) (n.hom)) : m = n :=
--     have p :  m.hom = n.hom := conj_eqToHom_iff_heq
--   WedgeMorphism.ext (conj_eqToHom_iff_heq _ _ (rfl) (rfl)).2 <| h_map _ _ f


attribute [simp] WedgeMorphism.fac

instance : Category (Wedge F) where
  Hom x y:=  WedgeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }


abbrev End :=  Σ w : Wedge F, Limits.IsTerminal w -- a transformer en categorie
abbrev Terminal :=  Σ x : C, Limits.IsTerminal x

-- def wr {a b : B} {c d : C} (fg : (a ⟶ b) × (c ⟶ d)) : (a,c) ⟶ (b,d):= (fg.1,fg.2)

def wedgeFromFctrHom {F G : (Bᵒᵖ×B) ⥤ M} (i: F ⟶ G) : Wedge F ⥤ Wedge G  where
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
  map {X Y} m := {
    hom := m.hom
    fac := fun c => by dsimp;rw [<-  m.fac c, Category.assoc ]}

lemma er (x : Wedge F): ((wedgeFromFctrHom (𝟙 F)).obj x).pt = x.pt := rfl
lemma er2 (x : Wedge F): ((wedgeFromFctrHom  (𝟙 F)).obj x) = x := by
    apply Wedge.ext
    · dsimp
      rfl
    · simp
      have : ((wedgeFromFctrHom (𝟙 F)).obj x).leg = x.leg := by
        funext c
        have h : ((wedgeFromFctrHom ((𝟙 F :  F ⟶ F))).obj x).leg c  = x.leg c ≫ ((𝟙 F :  F ⟶ F)).app (op c, c) := by rfl
        simp_all only [NatTrans.id_app, Category.comp_id]
      simpa [id_obj]

def wedgeFctr : (Bᵒᵖ×B ⥤ M) ⥤ Cat where
  obj f := Cat.of (Wedge f )
  map {f g } α := wedgeFromFctrHom α
  map_id f := by
    dsimp
    apply CategoryTheory.Functor.hext
    · intro x
      apply Wedge.ext
      · dsimp
        rfl
      · simp
        have : ((wedgeFromFctrHom (𝟙 f)).obj x).leg = x.leg := by
          funext c
          have h : ((wedgeFromFctrHom ((𝟙 f :  f ⟶ f))).obj x).leg c  = x.leg c ≫ ((𝟙 f :  f ⟶ f)).app (op c, c) := by rfl
          simp_all only [NatTrans.id_app, Category.comp_id]
        simpa [id_obj]
    · intro x y m
      dsimp
      -- let m1 : x ⟶ y := m
      -- let m1h : x.pt ⟶ y.pt := m.hom
      -- let m2 : (wedgeFromFctrHom f f (𝟙 f)).obj x ⟶ (wedgeFromFctrHom f f (𝟙 f)).obj y := ((wedgeFromFctrHom f f (𝟙 f)).map m)
      -- let m2h : x.pt ⟶ y.pt  := m2.hom
      -- let m2' := WedgeMorphism.mk m2h sorry
      -- have : m2h = m1h := rfl
      --apply WedgeMorphism.ext
      -- -- simpa using [WedgeMorphism.ext ]
      let as : x ⟶ y := eqToHom ((er2 f x).symm) ≫ (wedgeFromFctrHom (𝟙 f)).map m ≫ eqToHom (er2 f y)

      let hcast : (x ⟶ y) = ((wedgeFromFctrHom (𝟙 f)).obj x ⟶ (wedgeFromFctrHom (𝟙 f)).obj y) := by
        congr
        · exact (er2 f x).symm
        · exact (er2 f y).symm

      let asqw := cast hcast m
      let qsqrw := asqw.hom
      have asdq : asqw.hom = m.hom := by sorry

      let asqwq : (wedgeFromFctrHom (𝟙 f)).map m = asqw := by
        apply WedgeMorphism.ext
        sorry

      --HEq x:a y:b  equiv  cast x (a = b) = y : b
      let goal := HEq ((wedgeFromFctrHom (𝟙 f)).map m) m
      sorry
  map_comp := sorry


def isoWedgeFromFctrInv (G : (Bᵒᵖ×B) ⥤ M) (i: F ≅ G) : Wedge F ≅ Wedge G  where
  hom w := sorry
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


def natAsEnd (F G : A ⥤ B): End ( F.op.prod G ⋙ hom B) := ⟨natAsWedge F G, natAsWedgeIsTerminal F G⟩

def toEnd (F G : A ⥤ B) (α : NatTrans F G) : (natAsEnd F G).1.pt := α


-- advanced
-- "Nat(F,G)  ≃: End B(F-,G=)"  := (CC (End B(F-,G=))).mk (defaultEnd (Nat(F,G)))
-- "xpt : M ≃: Terminal C"   := (CC (Terminal C)).mk (defaultC x : C, isTerminal (defaultC x))

-- basic
-- "(natAsWedge F G, natAsEnd F G) ≃: End B(F-,G=)" = (CC (End B(F-,G=))).mk (natAsWedge F G, natAsEnd F G)
-- "(x : C, IsTerminal x)" ≃: Terminal C  := (CC (Terminal C)).mk (x : C, IsTerminal x)

-- def (≃:) (x : C, IsTerminal x)  :=
-- protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=  Quot.mk Setoid.r a

------------------------------------------------------------------------------------------------

section wedgeandcone
-- def end_ascone_aswedge_equiv [Limits.HasLimit ((CategoryOfElements.π (hom B)) ⋙ F)]
--     [Limits.HasTerminal (Wedge F)]: endAsCone F ≅ endAsWedge F  := sorry
end wedgeandcone
