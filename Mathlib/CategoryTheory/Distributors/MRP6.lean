import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic

namespace CategoryTheory

variable (A B C D : Type*) [Category A] [Category B] [Category C] [Category D]

abbrev Dist := Dᵒᵖ × C ⥤ Type

def times (P : Dist A B) (Q: Dist C D) :  Dist (A × C) (B × D) :=
  let plug  : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  :=
    Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙
    Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙
    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙
     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙
    (prod.inverseAssociator  _ _ _ )
  plug ⋙ Functor.prod P Q ⋙ MonoidalCategory.tensor Type

end CategoryTheory
