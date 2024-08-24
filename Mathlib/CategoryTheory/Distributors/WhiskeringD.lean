import Mathlib.CategoryTheory.EqToHom

open CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable (B : Type u₀) [Category.{v₀} B]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]


theorem whiskeringRight_comp {B : Type u₀} [Category.{v₀} B] (F : C ⥤ D) (G : D ⥤ E) :
    (whiskeringRight B C E).obj (F ⋙ G) =
    (whiskeringRight B C D).obj F ⋙ (whiskeringRight B D E).obj G := by
      apply Functor.hext (fun x => by rfl) (fun f g a => by
        simp_all only [whiskerRight_twice, whiskeringRight_obj_map, Functor.comp_map, heq_eq_eq])
