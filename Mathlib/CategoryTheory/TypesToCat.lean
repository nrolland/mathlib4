
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic


universe v u

namespace CategoryTheory

#check typeToCat

def disc  : Type u ⥤ Cat where -- cf def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun {X} {Y} f => by
    dsimp
    exact Discrete.functor (Discrete.mk ∘ f)
  map_id X := by
    apply Functor.ext
    · intro X Y f
      cases f
      simp only [id_eq, eqToHom_refl, Cat.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      aesop_cat
    · aesop_cat
  map_comp f g := by apply Functor.ext; aesop_cat

def Obj : Cat ⥤ Type u where
  obj X := X.α
  map := fun f => f.obj
  map_id X := by
    dsimp
    apply funext
    intro a
    rfl
  map_comp f g := by
    dsimp
    apply funext
    intro a
    rfl

section homEquiv

variable (X : Type u)
variable (Y : Cat)

def lxyToxry : (disc.obj X ⟶ Y) → (X ⟶ Obj.obj Y) := fun f x ↦ f.obj ⟨x⟩
def xryTolxy :  (X ⟶ Obj.obj Y) → (disc.obj X ⟶ Y) := fun f ↦ Discrete.functor f

def linverse : Function.LeftInverse (xryTolxy X Y) (lxyToxry X Y) := fun (fctr : disc.obj X ⥤ Y) ↦ by
  fapply Functor.hext
  . intro x; rfl
  . intro ⟨x⟩ ⟨y⟩ f
    simp
    obtain rfl := (Discrete.eq_of_hom f : x = y)
    calc
      (xryTolxy X Y (lxyToxry X Y fctr)).map f = 𝟙 (fctr.obj { as := x }) := Discrete.functor_map_id (xryTolxy X Y (lxyToxry X Y fctr)) f
      _                                        = fctr.map f := (Discrete.functor_map_id fctr f).symm

def rightinverse : Function.RightInverse (xryTolxy X Y) (lxyToxry X Y) := fun (f : X → Y ) ↦ by
  fapply funext
  intro x
  rfl

def homEquiv : ∀ X Y, (disc.obj X ⟶ Y) ≃ (X ⟶ Obj.obj Y) := fun X Y ↦ by
    apply Equiv.mk
      (lxyToxry X Y)
      (xryTolxy X Y)
      (linverse X Y)
      (rightinverse X Y)
end homEquiv


def counit_app : ∀ C,  (Obj ⋙ disc).obj C ⥤ C := fun C =>
    { obj := Discrete.as
      map := eqToHom ∘ Discrete.eq_of_hom }

def adj : disc ⊣ Obj where
  homEquiv : ∀ X Y, (disc.obj X ⟶ Y) ≃ (X ⟶ Obj.obj Y) := homEquiv
  unit : 𝟭 (Type u) ⟶ disc ⋙ Obj := { app:= fun X  ↦ Discrete.mk }
  counit : Obj ⋙ disc ⟶ 𝟭 Cat :=
  {
    app := counit_app
    naturality := by intro C D (f : C ⥤ D)
                     fapply Functor.hext
                     . intro c
                       rfl
                     . intro ⟨_⟩ ⟨_⟩ f
                       obtain rfl := Discrete.eq_of_hom f
                       aesop_cat
  }



end CategoryTheory
