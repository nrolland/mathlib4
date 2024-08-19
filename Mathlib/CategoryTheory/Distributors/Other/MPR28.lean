import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Hom

namespace CategoryTheory.Distributors
abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] := Bᵒᵖ × A ⥤ Type u
universe u
variable {A : Type u } [Category.{u} A]
variable {B : Type u } [Category.{u} B]
variable {C : Type u } [Category.{u} C]
variable {D : Type u } [Category.{u} D]

def opFunctor  :  (A ⥤ B)ᵒᵖ ⥤ (Aᵒᵖ ⥤ Bᵒᵖ)  where -- utility
  obj f := Functor.op (Opposite.unop f)
  map {fop gop : (A ⥤ B)ᵒᵖ} (nop : fop ⟶ gop) := {
    app := fun ao =>  Opposite.op ((Opposite.unop nop).app (Opposite.unop ao))
    naturality := fun _ _ uo => congrArg Quiver.Hom.op ((nop.unop.naturality uo.unop).symm) }

def prodFunctor : (A ⥤ B) × (C ⥤ D) ⥤ A × C ⥤ B × D where -- utility
  obj FG := FG.1.prod FG.2
  map nm :=  NatTrans.prod nm.1 nm.2


-- What I HAVE to write

def phi_ : (A ⥤ B) ⥤ Dist A B  :=
  (curry.obj prodFunctor).obj (𝟭 Bᵒᵖ) ⋙ (whiskeringRight _ _ _ ).obj (Functor.hom B)

def _phi : (A ⥤ B)ᵒᵖ ⥤  Dist B A :=
  opFunctor ⋙ (curry.obj (Prod.swap _ _ ⋙ prodFunctor )).obj (𝟭 B) ⋙
    (whiskeringRight _ _ _ ).obj (Functor.hom B)


-- What I want to write

def phi_' : (A ⥤ B) ⥤ Dist A B    :=
  prodFunctor ((𝟭 Bᵒᵖ), (·)) ⋙ Functor.hom B

def _phi' : (A ⥤ B)ᵒᵖ ⥤  Dist B A :=
  opFunctor ⋙ prodFunctor ((·)ᵒᵖ, (𝟭 B))  ⋙ Functor.hom B


end CategoryTheory.Distributors
