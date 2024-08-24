import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator

namespace CategoryTheory

@[pp_with_univ]
abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] :=
  Bᵒᵖ × A ⥤ Type u


section
universe v v₁ u u₁
variable {A : Type u₁ } [Category.{v₁} A]  -- all same unverses
variable {B : Type u₁ } [Category.{v₁} B]
variable {C : Type u₁ } [Category.{v₁} C]
variable {D : Type u₁ } [Category.{v₁} D]


def timesObj (P : Dist.{u}  A B) (Q: Dist.{v} C D) : (Bᵒᵖ × A) × Dᵒᵖ × C ⥤ Type u × Type v :=
  Functor.prod P Q

def timesFunctor : (Dist.{u} A B) × (Dist.{v} C D) ⥤  (Bᵒᵖ × A) × Dᵒᵖ × C ⥤ Type u × Type v    where
  obj := fun (P,Q) ↦ timesObj P Q
  map := sorry

def badCall (PQ : (Dist.{u} A B) × (Dist.{v} B C)) :
    (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
  := timesFunctor.obj.{v, v₁, u, u₁} PQ -- works

-- def badCall (PQ : (Dist.{u} A B) × (Dist.{v} B C)) :
--     (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
--   := timesFunctor.obj PQ -- failed to solve universe constraint


-- calling underlying implementation is ok
def nopb (PQ : (Dist.{u} A B) × (Dist.{v} B C)) :
    (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type v
  := timesObj PQ.1 PQ.2

--- works when v := u
def goodCall (PQ : (Dist.{u} A B) × (Dist.{u} B C)) :
    (Bᵒᵖ × A) × Cᵒᵖ × B ⥤ Type u × Type u
  := timesFunctor.obj PQ

end

end CategoryTheory
