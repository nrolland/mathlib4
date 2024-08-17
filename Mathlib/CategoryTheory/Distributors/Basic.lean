/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Distributors.Coend
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Combinatorics.Quiver.Basic
/-!
# Distributors

Distributors generalize functors like relations generalizes functions

## Notes

## TODO

## references

- Distributor at work
- Les distributeurs
-/
namespace CategoryTheory.Distributors

set_option linter.longLine false

open CategoryTheory
open MonoidalCategory
open Limits

@[pp_with_univ]
abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] := Bᵒᵖ × A ⥤ Type u

universe u
variable {A : Type u } [Category.{u} A]
variable {B : Type u } [Category.{u} B]
variable {C : Type u } [Category.{u} C]
variable {D : Type u } [Category.{u} D]
variable {E : Type u } [Category.{u} E]
def plugOne : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  := Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )
def plugTwo   : (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤  (B × C)ᵒᵖ × (A × B)  := (prod.inverseAssociator  _ _ _ ) ⋙ Functor.prod (Prod.swap _ _) (𝟭 _) ⋙ Functor.prod (prod.inverseAssociator _ _ _) (𝟭 _) ⋙ (prod.associator  _ _ _ ) ⋙ Functor.prod ((prodOpEquiv B).inverse) (𝟭 _)


def prodFunctor : (A ⥤ B) × (C ⥤ D) ⥤ A × C ⥤ B × D where
  obj FG := FG.1.prod FG.2
  map nm :=  NatTrans.prod nm.1 nm.2

-- @[simps]
-- protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
--   obj X := op (F.obj (unop X))
--   map f := (F.map f.unop).op


def prodFunctor' : (A ⥤ B) ⥤  (C ⥤ D) ⥤ A × C ⥤ B × D := curry.obj prodFunctor
def prodFunctor'' : (C ⥤ D) ⥤ (A ⥤ B) ⥤  A × C ⥤ B × D := curry.obj (Prod.swap _ _ ⋙ prodFunctor )

def phi_1 : (A ⥤ B) ⥤ ((Bᵒᵖ × A) ⥤ (Bᵒᵖ × B)) := prodFunctor'.obj (𝟭 Bᵒᵖ)
def phi_2 : ((Bᵒᵖ × A) ⥤ (Bᵒᵖ × B)) ⥤ (Bᵒᵖ × A ⥤ Type _) := (whiskeringRight _ _ _ ).obj (Functor.hom B)

def _phi1  :  (Aᵒᵖ ⥤ Bᵒᵖ ) ⥤ ((Aᵒᵖ × B) ⥤ (Bᵒᵖ × B))  := prodFunctor''.obj (𝟭 B)


-- /-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
-- instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
--   ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

def opFunctor  :  (A ⥤ B)ᵒᵖ ⥤ (Aᵒᵖ ⥤ Bᵒᵖ)  where
  obj f := Functor.op (Opposite.unop f)
  map {fop gop : (A ⥤ B)ᵒᵖ} (nop : fop ⟶ gop) := {
    app := fun ao =>  Opposite.op ((Opposite.unop nop).app (Opposite.unop ao))
    naturality := fun _ _ uo => congrArg Quiver.Hom.op ((nop.unop.naturality uo.unop).symm)
  }


def opFunctor  :  (A ⥤ B)ᵒᵖ ≌ (Aᵒᵖ ⥤ Bᵒᵖ)  where
  obj f := Functor.op (Opposite.unop f)
  map {fop gop : (A ⥤ B)ᵒᵖ} (nop : fop ⟶ gop) := {
    app := fun ao =>  Opposite.op ((Opposite.unop nop).app (Opposite.unop ao))
    naturality := fun _ _ uo => congrArg Quiver.Hom.op ((nop.unop.naturality uo.unop).symm)
  }


--def _phi2  :  ((Aᵒᵖ × B) ⥤ (Bᵒᵖ × B)) ⥤  (Aᵒᵖ × B ⥤ Type _)  := (whiskeringRight _ _ _ ).obj (Functor.hom B)

--- embeddings

def phi_ : (A ⥤ B) ⥤ ((Bᵒᵖ × A) ⥤ Type _) := prodFunctor'.obj (𝟭 Bᵒᵖ) ⋙ (whiskeringRight _ _ _ ).obj (Functor.hom B)

--- def whatIwant : (A ⥤ B) ⥤ ((Bᵒᵖ × A) ⥤ (Bᵒᵖ × B)) := prodFunctor ((𝟭 Bᵒᵖ), (·) )
--- def whatIwant' : (A ⥤ B) ⥤ ((Bᵒᵖ × A) ⥤ (Bᵒᵖ × B)) := prodFunctor ((·)ᵒᵖ, (𝟭 B))

-- def _phi : (A ⥤ B) ⥤ Dist B A := (curry.obj (Prod.swap _ _ ⋙ prodFunctor)).obj (𝟭 B)

def preimage  {X Y : (A ⥤ B)} (f : phi_.obj X ⟶ phi_.obj Y) : X ⟶ Y := sorry -- {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y

instance : Functor.FullyFaithful (@phi_ A _ B _ ) where
  map_preimage {X Y : (A ⥤ B)} (f : phi_.obj X ⟶ phi_.obj Y) : phi_.map (preimage f) = f := sorry
  preimage_map {X Y : (A ⥤ B)} (f : X ⟶ Y) : preimage (phi_.map f) = f := sorry


--- product

def timesObj (P : Dist.{u} A B) (Q: Dist.{u} C D) : Dist.{u} (A × C) (B × D) :=
  plugOne ⋙  P.prod Q ⋙ tensor (Type u)

def timesFunctor : (Dist.{u} A B) × ( Dist.{u} C D) ⥤ Dist.{u} (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := fun (a,b) ↦ whiskerLeft plugOne (whiskerRight (NatTrans.prod a b) (tensor (Type u)))


--- All the fields of the bicategory Dist (without talking of the bicategory Dist)
def homCategory : Category (Dist A B) := by infer_instance

def compObj (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  ((whiskeringRight _ _ _ ).obj myCoendPt).obj (curryObj (plugTwo ⋙ timesObj P Q))

def id  (B : Type u) [Category.{u} B] : Dist B B  := Functor.hom B

def compObj_id (P : Dist A B) : compObj P (id B) ≅ P := sorry  -- low level<< ninja (=yo emb + tensor) < FF emb

def comp : (Dist.{u} A B) × (Dist.{u} B C) ⥤  Dist.{u} A C  :=
  timesFunctor ⋙ (whiskeringLeft _ _  _ ).obj plugTwo ⋙ curry ⋙ (whiskeringRight _ _ _ ).obj myCoendPt

def whiskerLeft  (f : Dist A B ) {g h : Dist B C } (η : g ⟶ h) :
    comp.obj (f,g)  ⟶ comp.obj (f,h) := sorry -- from comp

def whiskerRight  {f g : Dist A B } (η : f ⟶ g) (h : Dist B C) :
    comp.obj (f,h)  ⟶ comp.obj (g,h) := sorry -- from comp

def associator  (f : Dist A B ) (g : Dist B C ) (h : Dist C D ) :
    (comp.obj (comp.obj (f,g),h)) ≅ (comp.obj (f, comp.obj (g,h)))
  := sorry

def leftUnitor (f : Dist A B ) : comp.obj (id A, f) ≅ f := sorry

def rightUnitor (f : Dist A B ) : comp.obj (f, id B) ≅ f := sorry

def whiskerLeft_id  (f : Dist A B ) (g : Dist B C ) : whiskerLeft f (𝟙 g) = 𝟙 (comp.obj (f,g)) := sorry

def whiskerLeft_comp  (f : Dist A B) {g h i : Dist B C} (η : g ⟶ h) (θ : h ⟶ i) :
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := sorry

def id_whiskerLeft  {f g : Dist A B} (η : f ⟶ g) :
      whiskerLeft (id A ) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := sorry

def comp_whiskerLeft (f : Dist A B) (g : Dist B C ) {h h' : Dist C D } (η : h ⟶ h') :
      whiskerLeft (comp.obj (f,g)) η =
        (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv := sorry

def id_whiskerRight   (f : Dist A B) (g : Dist B C) : whiskerRight (𝟙 f) g = 𝟙 (comp.obj (f,g)) := sorry

def comp_whiskerRight {f g h : Dist A B} (η : f ⟶ g) (θ : g ⟶ h) (i : Dist B C) :
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := sorry

def  whiskerRight_id  {f g : Dist A B} (η : f ⟶ g) :   whiskerRight η (id B ) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := sorry

def  whiskerRight_comp  {f f' : Dist A B} (η : f ⟶ f') (g : Dist B C) (h : Dist C D) :
     whiskerRight η (comp.obj (g,h)) =    (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom := sorry


def whisker_assoc (f : Dist A B) {g g' : Dist B C} (η : g ⟶ g') (h : Dist C D) :
      whiskerRight (whiskerLeft f η) h =    (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv :=  sorry

def whisker_exchange  {f g : Dist A B } {h i : Dist B C } (η : f ⟶ g) (θ : h ⟶ i) :
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := sorry

def pentagon  (f : Dist A B ) (g : Dist B C ) (h : Dist C D ) (i : Dist D E) :
      whiskerRight (associator f g h).hom i ≫
          (associator f (comp.obj (g, h)) i).hom ≫ whiskerLeft f (associator g h i).hom =
        (associator (comp.obj (f,g)) h i).hom ≫ (associator f g (comp.obj (h, i))).hom := sorry

def triangle (f : Dist A B ) (g : Dist B C ):
     (associator f (id B) g).hom ≫ whiskerLeft f (leftUnitor g).hom = whiskerRight (rightUnitor f).hom g := sorry

end CategoryTheory.Distributors
