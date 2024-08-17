import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements

open CategoryTheory

universe v₂ u₂ u
variable {B : Type u₂ } [Category.{v₂} B]

def Functor.ElementsFunctor  : (B ⥤ Type u) ⥤ Cat.{v₂, max u₂ u} where
  obj F := Cat.of.{v₂, max u₂ u} (F.Elements :  Type (max u₂ u) )
  map {F G} n := {
    obj := fun ⟨X,x⟩ ↦  ⟨X, n.app X x ⟩
    map := fun ⟨X, x⟩ {Y} ⟨f,_⟩ ↦
    match Y with | ⟨Y, y⟩ => ⟨f, by have := congrFun (n.naturality f) x;aesop_cat⟩
  }

def mycolimit  : (B ⥤ Type u) ⥤ Type (max u₂ u)
  := @Functor.ElementsFunctor B _ ⋙ Cat.connectedComponents

def mycoend : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B)) ⋙ mycolimit


#min_imports
