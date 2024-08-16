import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements

open CategoryTheory

universe v₂ u₂ u vm um
variable {B : Type u₂ } [Category.{v₂} B]
variable {M : Type vm } [Category.{um} M]
variable (F : (Bᵒᵖ×B) ⥤ M)

structure CoWedge : Type (max (max um u₂) vm) where
  pt : M
  leg (b:B) : F.obj (Opposite.op b,b) ⟶ pt
  cowedgeCondition : ∀ ⦃c c' : B⦄ (f : c ⟶ c'),
     (F.map (f.op, 𝟙 c) ≫ leg c : F.obj (Opposite.op c', c) ⟶  pt)  =
     (F.map ((𝟙 c').op, f) ≫ leg c'  : F.obj (Opposite.op c', c)  ⟶  pt) := by aesop_cat

structure CoWedgeMorphism (x y : CoWedge F) where
  Hom : x.pt ⟶ y.pt
  cowedgeCondition : ∀ (c : B), x.leg c ≫ Hom = y.leg c := by aesop_cat

attribute [simp] CoWedgeMorphism.cowedgeCondition

instance : Category (CoWedge F) where
  Hom := fun x y => CoWedgeMorphism _ x y
  id := fun x => {Hom := 𝟙 x.pt}
  comp := fun {X Y Z} f g => {
    Hom := f.Hom ≫ g.Hom
    cowedgeCondition := fun c => by rw [<- Category.assoc]; aesop_cat }

def NatTrans.mapElements {F G : B ⥤ Type _} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj := fun ⟨X, x⟩ ↦ ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f,h⟩ ↦ ⟨f, by have hb := congrFun (φ.naturality f) p.2; aesop_cat⟩

def Functor.ElementsFunctor : (B ⥤ Type u) ⥤ Cat.{v₂, max u₂ u} where
  obj F := Cat.of.{v₂, max u₂ u} (F.Elements :  Type (max u₂ u) )
  map {F G} n := {
    obj := fun ⟨X,x⟩ ↦  ⟨X, n.app X x ⟩
    map := fun ⟨X, x⟩ {Y} ⟨f,_⟩ ↦
    match Y with | ⟨Y, y⟩ => ⟨f, by have := congrFun (n.naturality f) x;aesop_cat⟩
  }

def myColimitPt : (B ⥤ Type u) ⥤ Type (max u₂ u)
  := @Functor.ElementsFunctor B _ ⋙ Cat.connectedComponents

----

def myCoendPt : (Bᵒᵖ × B ⥤  Type u) ⥤  Type (max u u₂) where
  obj F := ConnectedComponents F.Elements
  map {f g} n :=
    let as :  Cat.of f.Elements ⟶ Cat.of  g.Elements := NatTrans.mapElements n
    Cat.connectedComponents.map (as)
  map_id f := funext fun xq ↦ by obtain ⟨x,rfl⟩ := Quotient.exists_rep xq; rfl
  map_comp {f g h } n m := funext fun xq ↦ by obtain ⟨x,rfl⟩ := Quotient.exists_rep xq; rfl

def myOtherCoendPt : (Bᵒᵖ × B ⥤ Type u) ⥤  Type (max u u₂ v₂) :=
  (CategoryTheory.whiskeringLeft _ _ _ ).obj (CategoryOfElements.π (Functor.hom B)) ⋙ myColimitPt

def MyType := ∃ u, Type u

-- def they_might_be_equal  {B : Type u₂} [Category.{u₂, u₂} B] :
--   @myCoendPt.{u₂, u₂, u} B _ = @myOtherCoendPt.{u₂, u₂, u} B _ :=  sorry

-- def they_can't_be_equal  {B : Type u₂} [Category.{v₂, u₂} B] :
--   @myCoendPt.{v₂, u₂, u} B _ = @myOtherCoendPt.{v₂, u₂, u} B _  := sorry
-- -- type mismatch
-- --   myOtherCoendPt
-- -- has type
-- --   (Bᵒᵖ × B ⥤ Type u) ⥤ Type (max u u₂ v₂) : Type (max (max u u₂) (max (max u u₂) v₂) (max (max (max (u + 1) u₂) u) v₂) (max (u + 1) (u₂ + 1)) (v₂ + 1))
-- -- but is expected to have type
-- --   (Bᵒᵖ × B ⥤ Type u) ⥤ Type (max u u₂) : Type (max (max u u₂) (max (max (max (u + 1) u₂) u) v₂) (u + 1) (u₂ + 1))L
