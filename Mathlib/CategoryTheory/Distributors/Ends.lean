import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory
open Limits

universe v₁ v₂ vm u₁ u₂ u um
variable {J : Type u₁} [Category.{v₁} J]
-- variable {A : Type u₁ } [Category.{v₁} A]
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]



variable (F : (Bᵒᵖ×B) ⥤ M)

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

-- limits ---
set_option linter.longLine false
structure IsTerminalSimple (t : B) where
  lift : ∀ s : B, s ⟶ t
  uniq : ∀ (s : B) (m : s ⟶ t), m = lift s := by   aesop_cat

def IsTerminalUnique (t:B) := ∀ X : B, Unique (X ⟶ t)
def equiv1 (t:B) : (IsTerminalSimple t) ≅ IsTerminalUnique t where
  hom (ts) x := { default := ts.lift x, uniq := ts.uniq x}
  inv w := { lift := fun s => (w s).default, uniq := fun s => (w s).uniq}

def equiv2 (t : B) : (IsTerminalSimple t) ≅ IsLimit (asEmptyCone t ) where
  hom w :=  IsTerminal.ofUniqueHom (w.lift) (w.uniq)
  inv w := { lift := fun s =>  w.lift (asEmptyCone s)
             uniq :=  fun s m => w.uniq (asEmptyCone s) m (fun ⟨j⟩ => j.elim) }

def wr {a b : B} {i j : J} (fu : (a ⟶ b)  ×  (i ⟶ j)) : ((a,i) ⟶ (b,j)) := (fu.1, fu.2)


lemma wre {a b : B} {i j : J} (fg : (a,i) ⟶ (b,j)) : wr fg =  fg := rfl

def wrl  {a b c : B} {i j k : J} (fg : (a,i) ⟶ (b,j)) (u : b ⟶ c) (v : j ⟶ k) :
    fg ≫ wr (u, v ) = (fg.1 ≫ u, fg.2 ≫ v) := rfl


def awedgeisacone (w : Wedge F) : Cone (CategoryOfElements.π (Functor.hom B) ⋙ F ) := {
  pt := w.pt
  π := {
    app  := fun (⟨(bo,b'),f⟩) => w.leg bo.unop ≫ F.map (𝟙 bo, f)
    naturality := fun (⟨(bop,b'),f⟩) (⟨(cop,c'),g⟩)
      (⟨(uo, (v : b' ⟶ c') ),(h : (Functor.hom B).map (uo, v) f = g)⟩)  => by
        let b := bop.unop
        let c := cop.unop
        let u : c ⟶ b := uo.unop
        let f : b ⟶ b' := f
        let h :  u ≫ f ≫ v = g := h

        simp
        calc
        w.leg c ≫ F.map (𝟙 cop, g) =  w.leg c ≫ F.map (𝟙 cop, u ≫ f ≫ v) := by rw [<- h]
        _  =  w.leg c ≫ F.map ( wr (𝟙 cop, u ) ≫ wr (𝟙 cop, f ) ≫ wr (𝟙 cop, v) ) :=
          have :  (𝟙 cop ≫ 𝟙 cop ≫ 𝟙 cop, u ≫ f ≫ v) =  wr (𝟙 cop, u ) ≫ wr (𝟙 cop, f ) ≫ wr (𝟙 cop, v) := rfl
          have  : (𝟙 cop, u ≫ f ≫ v) =   wr (𝟙 cop, u ) ≫ wr (𝟙 cop, f ) ≫ wr (𝟙 cop, v) := by simp_all only [Category.comp_id]
          by rw [this]
        _  =  w.leg c ≫ F.map ( wr (𝟙 cop, u ) )≫ F.map (wr (𝟙 cop, f )) ≫ F.map  (wr (𝟙 cop, v) ) := by rw [F.map_comp, F.map_comp]
        _  = ( w.leg c ≫ F.map ( wr (𝟙 cop, u ) ))≫ F.map (wr (𝟙 cop, f )) ≫ F.map  (wr (𝟙 cop, v) ) := by rw [Category.assoc]
        _  =  (w.leg b ≫ F.map ( wr (uo, 𝟙 b ))) ≫ F.map (wr (𝟙 cop, f )) ≫ F.map (wr (𝟙 cop, v) ) := by
          have : (w.leg c ≫ F.map (wr (𝟙 cop, u))) = w.leg b ≫ F.map ( wr (uo, 𝟙 b )) := w.wedgeCondition u
          rw [this]
        _  =  w.leg b ≫ (F.map ( wr (uo, 𝟙 b )) ≫ F.map (wr (𝟙 cop, f )) ≫ F.map (wr (𝟙 cop, v) )) :=  by rw [Category.assoc]
        _  =  w.leg b ≫ ((F.map ( wr (uo, 𝟙 b )) ≫ F.map (wr (𝟙 cop, f ))) ≫ F.map (wr (𝟙 cop, v) )) :=  by rw [Category.assoc]
        _  =  w.leg b ≫ ((F.map (wr (uo, 𝟙 b ) ≫ wr (𝟙 cop, f ))) ≫ F.map (wr (𝟙 cop, v) )) := by rw [<- F.map_comp]
        _  =  w.leg b ≫ ((F.map (wr (uo, f ))) ≫ F.map (wr (𝟙 cop, v) )) := by
            have :  F.map (wr (uo, 𝟙 b )) ≫ F.map (wr (𝟙 cop, f )) =  F.map (wr (uo, 𝟙 b ) ≫ wr (𝟙 cop, f ))  := by rw [<- F.map_comp]
            have :  w.leg b ≫ ((F.map (wr (uo, 𝟙 b )) ≫ F.map (wr (𝟙 cop, f ))) ≫ F.map (wr (𝟙 cop, v) )) =  w.leg b ≫ ((F.map (wr (uo, f ))) ≫ F.map (wr (𝟙 cop, v) ))  := by
                  have :  F.map (wr (uo, 𝟙 b )) ≫ F.map ( wr (𝟙 cop, f )) = F.map (wr (uo, f ))  :=
                    have : wr (uo, 𝟙 b ) ≫ wr (𝟙 cop, f ) = wr (uo ≫ 𝟙 cop, 𝟙 b  ≫ f )  := rfl
                    by simp_all only [Category.comp_id,  Category.id_comp]
                  rw [this]
            simp_all only [Category.comp_id,  Category.id_comp]
        _ = w.leg b ≫ ( (F.map (wr (𝟙 bop, f ))≫ F.map ( wr (uo, 𝟙 b' ) )) ≫ F.map (wr (𝟙 cop, v) )) := by
          have :  w.leg b ≫ ((F.map (wr (uo, f ))) ≫ F.map (wr (𝟙 cop, v) )) =  w.leg b ≫ ( (F.map (wr (𝟙 bop, f ))≫ F.map ( wr (uo, 𝟙 b' ) )) ≫ F.map (wr (𝟙 cop, v) ))  := by
            have :   F.map ( wr (𝟙 bop, f )) ≫ F.map (wr (uo, 𝟙 b' )) = F.map (wr (uo, f ))     :=
              have soo :  wr (𝟙 bop, f ) ≫ wr (uo, 𝟙 b' ) = wr (𝟙 bop ≫ uo, f  ≫ 𝟙 b')  := rfl
              have aa : F.map ( wr (𝟙 bop, f )) ≫ F.map (wr (uo, 𝟙 b' )) = F.map ( wr (𝟙 bop, f ) ≫ wr (uo, 𝟙 b' )) := by rw [F.map_comp]
              by simp_all only [Category.comp_id, Category.id_comp]
            rw [<- this]
          simp_all only [Category.comp_id, Category.id_comp]
        _ = (w.leg b ≫  (F.map (wr (𝟙 bop, f ))))≫ F.map ( wr (uo, 𝟙 b' ) ) ≫ F.map (wr (𝟙 cop, v) ) := by  simp_all only [Category.assoc]
        _ = (w.leg b ≫  F.map (wr (𝟙 bop, f )))≫  F.map (wr (uo, v)) := by
            have a : wr (uo ≫ 𝟙 cop, 𝟙 b'  ≫ v ) = wr (uo , v )  := by simp_all only [Category.comp_id, Category.id_comp]
            have b : wr (uo, 𝟙 b' ) ≫ wr (𝟙 cop, v ) = wr (uo ≫ 𝟙 cop, 𝟙 b'  ≫ v )  := rfl
            have c : F.map ( wr (uo, 𝟙 b' )) ≫ F.map (wr (𝟙 cop, v) ) = F.map ( wr (uo, 𝟙 b' )≫ wr (𝟙 cop, v) ) := by rw [F.map_comp]
            rw [c, b , a ]
        _ = w.leg b ≫ F.map (𝟙 bop, f) ≫ F.map (uo, v)    :=  by rw [<- Category.assoc];rfl
        }
}


-- missing : a wedge for F is a cone for F . pi
-- missing : un wedge pour F est un cone pour F . p
-- missing : un terminal wedge pour F est terminal cone pour F . p -- terminal + iso
-- missing Nat(F,G) ≅ end B(F-,G=)



---



/-- end is a terminal wedges -/
noncomputable def end_summit [HasTerminal (Wedge F)] := terminal (Wedge F)

def endCone [Limits.HasLimit ((CategoryOfElements.π (Functor.hom B)) ⋙ F)] : Type _ :=
  Limits.LimitCone ((CategoryOfElements.π (Functor.hom B)) ⋙ F)
