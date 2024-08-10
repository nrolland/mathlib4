import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor

namespace CategoryTheory


universe v₁ v₂ v₃ u₁ u₂

variable (A B C D: Cat)

variable {C : Type u₂} [Category.{u₁} C]

-- variable (A B C D) [Category A] [Category B] [Category C] [Category D]

def t : B × Cᵒᵖ × A ⥤ (B × Cᵒᵖ) × A := (prod.inverseAssociator  B Cᵒᵖ A)

def tt :  B × (B × (Cᵒᵖ × A)) ⥤  B × ((B × Cᵒᵖ) × A)  := Functor.prod (𝟭 B) (prod.inverseAssociator  B Cᵒᵖ A)
