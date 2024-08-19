import Mathlib.CategoryTheory.Elements
open CategoryTheory
open CategoryOfElements
open Functor
open Opposite

-- 1 - I write some definition
------------------------------------------------------------------------------------------------
section wedge
universe v₂ vm u₂  um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type um } [Category.{vm} M]

structure Wedge (F : (Bᵒᵖ×B) ⥤ M) :  Type (max u₂ um vm) where
  pt : M
  leg (c:B) : pt ⟶ F.obj (op c,c)
  wedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
    (leg c ≫ F.map ((𝟙 c).op,f) : pt ⟶ F.obj (op c, c'))
     = (leg c' ≫ F.map (f.op, 𝟙 c')  : pt ⟶ F.obj (op c, c')) := by aesop_cat

end wedge

-- 2 - I try to use the definition
------------------------------------------------------------------------------------------------
section trying_to_use
universe v₂ v₃  u₂ u₃
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]


def natAsEnd (F G : B ⥤ C): Wedge ( F.op.prod G ⋙ hom C)  := {
  pt := NatTrans F G -- I find that the constraint solvers can't unify  : v3 = max v3 u2
  leg := sorry
  wedgeCondition := sorry
}
end trying_to_use


-- 3- So I set u2 = v3, it works
------------------------------------------------------------------------------------------------
universe v₂ v₃  u₂ u₃
variable {B : Type v₃ } [Category.{v₂} B]
variable {C : Type u₃ } [Category.{v₃} C]

def natTrans  (F G : B ⥤ C) := (NatTrans F G : Type _ )
def CFG  (F G : B ⥤ C) :  Bᵒᵖ × B ⥤ Type v₃ := F.op.prod G ⋙ hom C

def natAsEndsad (F G : B ⥤ C) : Type _  :=  Wedge (F.op.prod G ⋙ hom C)

def natAsEnd2 (F G : B ⥤ C): Wedge ( F.op.prod G ⋙ hom C)  := {
  pt := natTrans F G
  leg := sorry
  wedgeCondition := sorry
}
