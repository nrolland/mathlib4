
import Mathlib.CategoryTheory.Distributors.Ends
import Mathlib.CategoryTheory.Distributors.Coends
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory
open Limits

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)

-- bientot  Mathlib/CategoryTheory/Elements.lean
def NatTrans.mapElements {F G : B ⥤ Type _} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj := fun ⟨X, x⟩ ↦ ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f,h⟩ ↦ ⟨f, by have hb := congrFun (φ.naturality f) p.2; aesop_cat⟩
-- bientot Mathlib/CategoryTheory/Elements.lean
def Functor.ElementsFunctor : (B ⥤ Type u) ⥤ Cat.{v₂, max u₂ u} where
  obj F := Cat.of.{v₂, max u₂ u} (F.Elements :  Type (max u₂ u) )
  map {F G} n := {
    obj := fun ⟨X,x⟩ ↦  ⟨X, n.app X x ⟩
    map := fun ⟨X, x⟩ {Y} ⟨f,_⟩ ↦
    match Y with | ⟨Y, y⟩ => ⟨f, by have := congrFun (n.naturality f) x;aesop_cat⟩}


--------------------------------------------------------------------------------------------------

def myCoendPt : (Bᵒᵖ × B ⥤  Type u) ⥤  Type (max u₂ u) where
  obj F := ConnectedComponents F.Elements -- je calcule
  map {f g} n :=
    let as :  Cat.of f.Elements ⟶ Cat.of  g.Elements := NatTrans.mapElements n
    Cat.connectedComponents.map (as)
  map_id f := funext fun xq ↦ by obtain ⟨x,rfl⟩ := Quotient.exists_rep xq; rfl
  map_comp {f g h } n m := funext fun xq ↦ by obtain ⟨x,rfl⟩ := Quotient.exists_rep xq; rfl

/-- Each nadir is a cowedge -/
def myCoendObj (F : Bᵒᵖ × B ⥤ Type (max u u₂)) : (CoWedge F : Type (max (u + 1) (u₂ + 1)))  where
  pt := myCoendPt.obj F -- je calcule
  leg b x := Quotient.mk _ ⟨(Opposite.op b, b),x⟩
  cowedgeCondition b b' f  := funext (fun x ↦
    have z1 : @Zigzag (F.Elements) _  ⟨(Opposite.op b, b), F.map (f.op, 𝟙 b) x⟩ _  :=
      Zigzag.of_inv ⟨(f.op, 𝟙 b),rfl⟩
    have z2 : @Zigzag (F.Elements) _  ⟨(Opposite.op b', b), x⟩ _ :=
      Zigzag.of_hom ⟨((𝟙 b').op, f),rfl⟩
    Quotient.sound ((z1).trans z2))

-- missing : this cowedege is initial in Cowedges

def colimitNadirFunctor : (B ⥤ Type u) ⥤ Type (max u₂ u) :=
  @Functor.ElementsFunctor B _ ⋙ Cat.connectedComponents -- je calcule

-- missing : this is initial cocone

def myCoendPt' : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) := -- je calcule
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B)) ⋙ colimitNadirFunctor

-- missing : the corresponding cowedge for F is initial

--------------------------------------------------------------------------------------------------


def myEndPt : (Bᵒᵖ × B ⥤  Type u) ⥤  Type (max u₂ u) where
  obj F := sorry
  map {f g} n := sorry
  map_id f := sorry
  map_comp {f g h } n m := sorry

/-- Each summit is a wedge -/
def myEndObj (F : Bᵒᵖ × B ⥤ Type (max u u₂)) : (Wedge F : Type _)  where
  pt := sorry
  leg b x := sorry
  wedgeCondition b b' f  := sorry

-- missing : this wedge is terminal in Wedge

def myLimitPt : (B ⥤ Type u) ⥤ Type (max u₂ u)
  := sorry

-- missing : this is terminal cone tip

def end_summit' : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B)) ⋙ myLimitPt


-- missing : the corresponding wedge is termina


--------------------------------------------------------------------------------------------------

variable {A : Type u₂ } [Category.{v₂} A]


-- def NatIsCoend {f : A ⥤ B} {g : A ⥤ B} :
--   (Quiver.Hom (A ⥤ B) _ f g ) = End () := sorry
