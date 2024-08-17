import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Comma.Basic


open CategoryTheory


universe  v₃ u₃ u
variable (C : Type u₃ ) [Category.{v₃} C]
universe v₂ u₂
variable {B : Type u₂ } [Category.{v₂} B]
universe  v₄ u₄
variable (X : Type u₄  ) [Category.{v₄}  X]




def bopb := Cat.of.{v₂,u₂} Bᵒᵖ × B
def elebopb := Cat.of.{v₂,u₂} Bᵒᵖ × B

def asd :  Bᵒᵖ × B ⥤ Type v₂  := Functor.hom B
def asdasd : Type (max u₂ v₂)  := (Functor.hom B).Elements
def asdasa : Cat.{v₂, (max u₂ v₂)}  := Cat.of (Functor.hom B).Elements



def Functor.ElementsFunctor :  (C ⥤ Type u) ⥤ Cat.{v₃, max u₃ u} where
  obj F := Cat.of.{v₃, max u₃ u} (F.Elements :  Type (max u₃ u) )
  map {F G} n := {
    obj := fun ⟨X,x⟩ ↦  ⟨X, n.app X x ⟩
    map := fun ⟨X, x⟩ {Y} ⟨f,_⟩ ↦
    match Y with | ⟨Y, y⟩ => ⟨f, by have := congrFun (n.naturality f) x;aesop_cat⟩
  }


def cc.{v, u_2} : Cat.{v, u_2} ⥤ Type u_2 := Cat.connectedComponents


def mycolimit : (C ⥤ Type u) ⥤  Type (max u₃ u) :=
  let one : (C ⥤ Type u) ⥤ Cat.{v₃, max u₃ u}  := Functor.ElementsFunctor C
  let two :  Cat.{v₃, max u₃ u} ⥤ Type (max u₃ u) := cc.{v₃, max u₃ u}
  one ⋙ two


def myprecomp  : (Bᵒᵖ × B ⥤ Type u) ⥤  (Functor.hom B).Elements ⥤ Type u :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B))


def mycoend_ : (Bᵒᵖ × B ⥤ Type u) ⥤  Type _ :=
  let one : (Bᵒᵖ × B ⥤ Type u) ⥤  (Functor.hom B).Elements ⥤ Type u := myprecomp
  let two : ((Functor.hom B).Elements ⥤ Type u) ⥤  Type (max ((max u₂ v₂)) u) :=
     mycolimit ((Functor.hom B).Elements)
  one ⋙ two

def mycoend : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max (max u u₂) v₂) :=
  myprecomp ⋙ mycolimit ((Functor.hom B).Elements)



section withhiddenC

def mycolimit' {C : Type u₃ } [Category.{v₃} C] : (C ⥤ Type u) ⥤  Type (max u₃ u) := mycolimit C

def mycoend' : (Bᵒᵖ × B ⥤ Type u) ⥤  Type _ :=   myprecomp ⋙ mycolimit'

end withhiddenC
