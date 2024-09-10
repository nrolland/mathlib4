/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Distributors.Ends
import Mathlib.CategoryTheory.Distributors.Coends
import Mathlib.CategoryTheory.Distributors.FunctorD
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
open Functor

@[pp_with_univ]
abbrev Dist.{u, v₂, u₂, v₁, u₁} (A : Type u₁) [Category.{v₁} A] (B : Type u₂ ) [Category.{v₂} B] := Bᵒᵖ × A ⥤ Type u

universe v u
variable {A : Type u } [Category.{u} A]
variable {B : Type u } [Category.{u} B]
variable {C : Type u } [Category.{u} C]
variable {D : Type u } [Category.{u} D]
variable {E : Type u } [Category.{u} E]
def plugOne : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  := Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )
def plugTwo   : (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤  (B × C)ᵒᵖ × (A × B)  := (prod.inverseAssociator  _ _ _ ) ⋙ Functor.prod (Prod.swap _ _) (𝟭 _) ⋙ Functor.prod (prod.inverseAssociator _ _ _) (𝟭 _) ⋙ (prod.associator  _ _ _ ) ⋙ Functor.prod ((prodOpEquiv B).inverse) (𝟭 _)


def hat : Dist A B ⥤ A ⥤ (Bᵒᵖ ⥤ Type u)  := sorry -- TODO


-- --- product

def timesObj (P : Dist.{u} A B) (Q: Dist.{u} C D) : Dist.{u} (A × C) (B × D) :=
  plugOne ⋙  P.prod Q ⋙ tensor (Type u)

def timesFunctor : (Dist.{u} A B) × ( Dist.{u} C D) ⥤ Dist.{u} (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := fun (a,b) ↦ whiskerLeft plugOne (whiskerRight (NatTrans.prod a b) (tensor (Type u)))


-- --- All the fields of the bicategory Dist (without talking of the bicategory Dist)
def homCategory : Category (Dist A B) := by infer_instance

def compObj (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  ((whiskeringRight _ _ _ ).obj myCoendPt).obj (curryObj (plugTwo ⋙ timesObj P Q))

def id  (B : Type u) [Category.{u} B] : Dist B B  := Functor.hom B

-- def compObj_id (P : Dist A B) : compObj P (id B) ≅ P := sorry  -- low level<< ninja (=yo emb + tensor) < FF emb

-- def comp : (Dist.{u} A B) × (Dist.{u} B C) ⥤  Dist.{u} A C  :=
--   timesFunctor ⋙ (whiskeringLeft _ _  _ ).obj plugTwo ⋙ curry ⋙ (whiskeringRight _ _ _ ).obj myCoendPt


--- embeddings
def phi_ : (A ⥤ B) ⥤ Dist A B  := (curry.obj prodFunctor).obj (𝟭 Bᵒᵖ) ⋙ (whiskeringRight _ _ _ ).obj (Functor.hom B)

def _phi : (A ⥤ B)ᵒᵖ ⥤  Dist B A := Functor.opHom _ _ ⋙ (curry.obj (Prod.swap _ _ ⋙ prodFunctor )).obj (𝟭 B) ⋙ (whiskeringRight _ _ _ ).obj (Functor.hom B)

-- def reduce (F : A ⥤ B ) (G : A ⥤ B) : compObj (_phi.obj F) (phi_ G) ≅ F.op.prod G ⋙ hom _


def isoFG (F : A ⥤ B ) (G : A ⥤ B) : NatTrans F G ≅ NatTrans (phi_.obj F) (phi_.obj G) :=
  let w : Ends (F.op.prod G ⋙ hom _) := natAsEnd F G --  (NatTrans F G) ∈ Ends B(F-,G=)
  let y : Ends (F.op.prod G ⋙ hom _) ≅ Ends ((hat.obj (phi_.obj F)).op.prod (hat.obj (phi_.obj G)) ⋙ hom _) :=
    let yo : (F.op.prod G ⋙ hom _) ≅ ((hat.obj (phi_.obj F)).op.prod (hat.obj (phi_.obj G)) ⋙ hom _) := sorry
    sorry
  let natasEndyo := natAsEnd (phi_.obj F) (phi_.obj G) --  NatTrans (phi_.obj F) (phi_.obj G) ∈ Ends [B,Set](B(,G=),B(,G=))
  -- Donc
  -- (NatTrans F G) ≅ yo ((NatTrans F G)) ∈ Ends [B,Set](B(,G=),B(,G=))
  -- NatTrans (phi_.obj F) (phi_.obj G) ∈ Ends [B,Set](B(,G=),B(,G=))
  -- Donc
  -- yo ((NatTrans F G)) ≅ NatTrans (phi_.obj F) (phi_.obj G)
  -- Finalement
  -- (NatTrans F G) ≅ yo ((NatTrans F G)) ≅ NatTrans (phi_.obj F) (phi_.obj G)


  -- VS : composition d'isos
  --  (NatTrans F G) ≅ Ends B(F-,G=) ≅ Ends [B,Set](B(,G=),B(,G=)) ≅ NatTrans (phi_.obj F) (phi_.obj G))
  sorry

def preimage  {X Y : (A ⥤ B)} (f : phi_.obj X ⟶ phi_.obj Y) : X ⟶ Y := sorry -- {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y

instance : Functor.FullyFaithful (@phi_ A _ B _ ) where
  map_preimage {X Y : (A ⥤ B)} (f : phi_.obj X ⟶ phi_.obj Y) : phi_.map (preimage f) = f := sorry
  preimage_map {X Y : (A ⥤ B)} (f : X ⟶ Y) : preimage (phi_.map f) = f := sorry




-- def whiskerLeft  (f : Dist A B ) {g h : Dist B C } (η : g ⟶ h) :
--     comp.obj (f,g)  ⟶ comp.obj (f,h) := sorry -- from comp

-- def whiskerRight  {f g : Dist A B } (η : f ⟶ g) (h : Dist B C) :
--     comp.obj (f,h)  ⟶ comp.obj (g,h) := sorry -- from comp

-- def associator  (f : Dist A B ) (g : Dist B C ) (h : Dist C D ) :
--     (comp.obj (comp.obj (f,g),h)) ≅ (comp.obj (f, comp.obj (g,h)))
--   := sorry

-- def leftUnitor (f : Dist A B ) : comp.obj (id A, f) ≅ f := sorry

-- def rightUnitor (f : Dist A B ) : comp.obj (f, id B) ≅ f := sorry

-- def whiskerLeft_id  (f : Dist A B ) (g : Dist B C ) : whiskerLeft f (𝟙 g) = 𝟙 (comp.obj (f,g)) := sorry

-- def whiskerLeft_comp  (f : Dist A B) {g h i : Dist B C} (η : g ⟶ h) (θ : h ⟶ i) :
--       whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := sorry

-- def id_whiskerLeft  {f g : Dist A B} (η : f ⟶ g) :
--       whiskerLeft (id A ) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := sorry

-- def comp_whiskerLeft (f : Dist A B) (g : Dist B C ) {h h' : Dist C D } (η : h ⟶ h') :
--       whiskerLeft (comp.obj (f,g)) η =
--         (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv := sorry

-- def id_whiskerRight   (f : Dist A B) (g : Dist B C) : whiskerRight (𝟙 f) g = 𝟙 (comp.obj (f,g)) := sorry

-- def comp_whiskerRight {f g h : Dist A B} (η : f ⟶ g) (θ : g ⟶ h) (i : Dist B C) :
--       whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := sorry

-- def  whiskerRight_id  {f g : Dist A B} (η : f ⟶ g) :   whiskerRight η (id B ) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := sorry

-- def  whiskerRight_comp  {f f' : Dist A B} (η : f ⟶ f') (g : Dist B C) (h : Dist C D) :
--      whiskerRight η (comp.obj (g,h)) =    (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom := sorry


-- def whisker_assoc (f : Dist A B) {g g' : Dist B C} (η : g ⟶ g') (h : Dist C D) :
--       whiskerRight (whiskerLeft f η) h =    (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv :=  sorry

-- def whisker_exchange  {f g : Dist A B } {h i : Dist B C } (η : f ⟶ g) (θ : h ⟶ i) :
--       whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := sorry

-- def pentagon  (f : Dist A B ) (g : Dist B C ) (h : Dist C D ) (i : Dist D E) :
--       whiskerRight (associator f g h).hom i ≫
--           (associator f (comp.obj (g, h)) i).hom ≫ whiskerLeft f (associator g h i).hom =
--         (associator (comp.obj (f,g)) h i).hom ≫ (associator f g (comp.obj (h, i))).hom := sorry

-- def triangle (f : Dist A B ) (g : Dist B C ):
--      (associator f (id B) g).hom ≫ whiskerLeft f (leftUnitor g).hom = whiskerRight (rightUnitor f).hom g := sorry

end CategoryTheory.Distributors
