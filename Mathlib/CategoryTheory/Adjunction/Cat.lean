/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions related to Cat, the category of categories

The embedding `Type ⥤ Cat` has a right adjoint `Cat.objects` mapping
each category to its set of objects.


## TODO
The embedding `Type ⥤ Cat` has a left adjoint `Cat.connectedComponents` mapping
each category to its set of connected components.

-/


universe v u

namespace CategoryTheory

section AdjDiscObj

variable (X : Type u)
variable (C : Cat)

private def lxyToxry : (typeToCat.obj X ⟶ C) → (X ⟶ Cat.objects.obj C) := fun f x ↦ f.obj ⟨x⟩
private def xryTolxy : (X ⟶ Cat.objects.obj C) → (typeToCat.obj X ⟶ C) := fun f ↦ Discrete.functor f

private lemma linverse : Function.LeftInverse (xryTolxy X C) (lxyToxry X C) :=
  fun (fctr : typeToCat.obj X ⥤ C) ↦ by
  fapply Functor.hext
  · intro x; rfl
  · intro ⟨x⟩ ⟨y⟩ f
    simp
    obtain rfl := (Discrete.eq_of_hom f : x = y)
    calc
      (xryTolxy X C (lxyToxry X C fctr)).map f = 𝟙 (fctr.obj { as := x }) :=
        Discrete.functor_map_id (xryTolxy X C (lxyToxry X C fctr)) f
      _                                        = fctr.map f := (Discrete.functor_map_id fctr f).symm

private lemma rightinverse : Function.RightInverse (xryTolxy X C) (lxyToxry X C) := fun _ ↦ by
  fapply funext
  intro x
  rfl

private def homEquiv : ∀ X C, (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) := fun X C ↦ by
    apply Equiv.mk
      (lxyToxry X C)
      (xryTolxy X C)
      (linverse X C)
      (rightinverse X C)

private def counit_app : ∀ C,  (Cat.objects ⋙ typeToCat).obj C ⥤ C := fun C =>
    { obj := Discrete.as
      map := eqToHom ∘ Discrete.eq_of_hom }


/-- typeToCat : Type ⥤ Cat is left adjoint to Cat.objects : Cat ⥤ Type
-/
def adjTypeToCatCatobjects : typeToCat ⊣ Cat.objects where
  homEquiv  := homEquiv
  unit : 𝟭 (Type u) ⟶ typeToCat ⋙ Cat.objects := { app:= fun X  ↦ Discrete.mk }
  counit : Cat.objects ⋙ typeToCat ⟶ 𝟭 Cat :=
  {
    app := counit_app
    naturality := by intro C D (f : C ⥤ D)
                     fapply Functor.hext
                     · intro c
                       rfl
                     · intro ⟨_⟩ ⟨_⟩ f
                       obtain rfl := Discrete.eq_of_hom f
                       aesop_cat
  }

-- /-- The equivalence of categories `(J → C) ≌ (Discrete J ⥤ C)`. -/
-- @[simps]
-- def piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C] :
--                                  (J → C) ≌ (Discrete J ⥤ C) where
--   functor :=
--     { obj := fun F => Discrete.functor F
--       map := fun f => Discrete.natTrans (fun j => f j.as) }
--   inverse :=
--     { obj := fun F j => F.obj ⟨j⟩
--       map := fun f j => f.app ⟨j⟩ }
--   unitIso := Iso.refl _
--   counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun j => Iso.refl _)
--     (by
--       rintro ⟨x⟩ ⟨y⟩ f
--       obtain rfl : x = y := Discrete.eq_of_hom f
--       obtain rfl : f = 𝟙 _ := rfl
--       simp))) (by aesop_cat)

end AdjDiscObj


section AdjCC



section techniques
variable (X)
variable {C D : Cat}
variable {α : Type u}
variable {a b : C}
variable (F : C ⥤ D)

/-! # Relation induced by a category

A category induces a relation on its objects
Two objects are connected if there is an arrow between them.
This relation is not an equivalence, as only reflexivity holds in general.

`{a:C}{b:C} (f : a ⟶ b) : isConnected a b := ⟨f, trivial⟩`
-/
def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True

/--
The relation is transported by functors
-/
lemma transport (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
   obtain ⟨f,_⟩ := h
   exact ⟨F.map f, trivial⟩


/-! ## Relation induced by a category

To make this relation an equivalence, one needs to take the equivalence closure
Two objects are connected if there is a zigzag of arrows between them.

-/
abbrev isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

private def relzz (f : a ⟶ b) : isConnectedByZigZag a b := EqvGen.rel _ _ (⟨f, trivial⟩)


lemma transportExt  (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w
  case trans f g => exact EqvGen.trans _ _ _ f g

-- Other formulation
-- def isConnectedByQuotEq (a b : C) := Quot.mk isConnected a = Quot.mk isConnected  b
-- lemma functorialityQuotClosed : isConnectedByQuotEq a b →
--                                 isConnectedByQuotEq (F.obj a) (F.obj b) :=
--    Quot.EqvGen_sound ∘ transportExt F ∘ Quot.exact isConnected

--- Quotient based computation
def catisSetoid : Setoid C where
  r := EqvGen isConnected
  iseqv := EqvGen.is_equivalence isConnected


private def relsetoid (f : a ⟶ b) : EqvGen isConnectedByZigZag a b := EqvGen.rel _ _ (relzz f )

-- Transport d'un x vers sa composante
def toCC (x : C) : Quotient (@catisSetoid C) := Quotient.mk (@catisSetoid C) x

private def releqq (f : a ⟶ b) : toCC a = toCC b := Quot.EqvGen_sound (relsetoid f)


-- Ensemble des composantes d'une categorie
abbrev ccSet  (C : Cat) := Quotient (@catisSetoid C)

lemma transportExtQuot (a b : C) : isConnectedByZigZag a b → toCC (F.obj a) = toCC (F.obj b) :=
    Quot.sound ∘ transportExt F

private def fmap {X Y : Cat} (F : X ⟶ Y) : (ccSet X) → (ccSet Y) :=
    Quotient.lift (s:= @catisSetoid X)
                  (toCC ∘ F.obj  : X → ccSet Y)
                  (fun _ _ => Quot.sound ∘ transportExt F )

private abbrev liftedMk (s : Setoid α)  := Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)

private def quotDecomp {s : Setoid α}  : ∀ xt : Quotient s, (∃ x, ⟦x⟧ = xt) :=
  Quotient.ind (motive:= (∃ x, Quotient.mk s x = ·)) (by simp; exact ⟨·, s.refl _⟩)

/- The functor for connected components -/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ccSet C -- maps a category to its set of CC
  map F := fmap F  -- transport a functor to a function beetwen CC
  map_id X := by calc
      fmap (𝟙 X) =  liftedMk (@catisSetoid X) := (rfl : fmap (𝟙 X) = liftedMk (@catisSetoid X))
      _                       = fun x => x    := by funext xt; obtain ⟨x,h⟩ := quotDecomp xt
                                                    simp [h.symm]
      _                       = 𝟙 (ccSet X)   := by rfl
  map_comp f g := by simp; funext xt; obtain ⟨_,h⟩ := quotDecomp xt;
                     simp [h.symm];rfl

def eq_of_zigzag {a b : typeToCat.obj X } (h : isConnectedByZigZag a b) : a.as = b.as := by
  induction h with
  | rel _ _ h => let ⟨f,_⟩ := h;exact Discrete.eq_of_hom f
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

def transportZigzag (F : C ⥤ D) (h : isConnectedByZigZag a b)
             : isConnectedByZigZag (F.obj a) ( F.obj b) := by
  induction h with
  | rel _ _ h => let ⟨f,_⟩ := h; exact EqvGen.rel _ _  ⟨F.map f, trivial⟩
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

end techniques


section adjunctionCC
variable (X : Type u)
variable (C D : Cat)

def laxToarx : (connectedComponents.obj C ⟶ X) → (C ⥤ typeToCat.obj X) := fun fct =>
  { obj := fun x => x |> toCC |> fct |> Discrete.mk
    map := fun {a b} f => Discrete.eqToHom (congrArg fct (releqq f))
    map_id := by simp
    map_comp := by simp
  }


def arxTolax :  (C ⥤ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := fun fctr  =>
  Quotient.lift (s:= (@catisSetoid C))
     (fun c => (fctr.obj c).as)
     (fun _ _ h => eq_of_zigzag X (transportZigzag fctr h))

set_option linter.longLine false

private def linverse' : Function.LeftInverse (arxTolax X C ) (laxToarx X C ) :=
  fun (f : connectedComponents.obj C ⟶ X) => by
    funext xcc
    obtain ⟨x,h⟩ := quotDecomp xcc
    calc
      arxTolax X C (laxToarx X C f) xcc =  arxTolax X C (laxToarx X C f) ⟦x⟧ := by rw [<- h]
      _  = ((laxToarx X C f).obj x).as := rfl
      _  = f ⟦x⟧ := rfl
      _  = f xcc := by rw [h]

private def rinverse' : Function.RightInverse (arxTolax X C ) (laxToarx X C ) :=
  fun (fctr : C ⥤ (typeToCat.obj X)) => by
    fapply Functor.hext
    · intro c; rfl
    · intro c d f
      have cdeq : fctr.obj c = fctr.obj d := f |> fctr.map |> Discrete.eq_of_hom |> congrArg Discrete.mk
      let ident : (discreteCategory X).Hom (fctr.obj c) (fctr.obj d) := by rw [cdeq]; exact 𝟙 _
      let p := Subsingleton.helim rfl ident ((laxToarx X C (arxTolax X C fctr)).map f)
      exact (p.symm).trans (Subsingleton.helim rfl ident (fctr.map f) : HEq ident (fctr.map f))



def rwmorph {a b x : C} (h : x = a ) (f : a ⟶ b)  : x ⟶ b := by rw [h]; exact f
-- theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=  i.down.down


def asd {a b : C} (this : Discrete.mk (toCC a) = Discrete.mk (toCC b)) := rwmorph (.of (Discrete (ccSet C ))) this (𝟙 (Discrete.mk (toCC b)))

-- 3 different ways of app
def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := fun C X  ↦ {
    toFun := laxToarx X C
    invFun  := arxTolax X C
    left_inv  := linverse' X C --: LeftInverse invFun toFun
    right_inv  := rinverse' X C  --: RightInverse invFun toFun
    }
  unit : 𝟭 Cat ⟶ connectedComponents ⋙ typeToCat :=
    {
      -- 3 different ways of app
      app:= fun C  ↦ laxToarx _ _ (𝟙 (ccSet C))

      -- app:= fun C  ↦  { obj := fun x => x |> Quotient.mk (@catisSetoid C) |> Discrete.mk
      --                   map := fun {a b} f => Discrete.eqToHom ( (releqq f))
      --                   map_id := by simp
      --                   map_comp := by simp
      --                 }

      --app:= fun C  ↦ laxToarx (ccSet C) C (𝟙 (ccSet C))
      -- app:= fun C  ↦ {
      --     obj := fun c => c |> toCC |> Discrete.mk
      --     map := fun {a b} f => by simp; rw [releqq f]; exact 𝟙 _
      --     map_id := by simp
      --     map_comp := fun f g => by have :=releqq f ; have := releqq g; aesop_cat
      --     }
    }
  counit : typeToCat ⋙ connectedComponents ⟶ 𝟭 (Type u) :=  {
      app := fun X => arxTolax X (typeToCat.obj X) (𝟙 (typeToCat.obj X) : typeToCat.obj X ⥤ typeToCat.obj X)
      naturality := fun X Y f => by
        funext xcc
        obtain ⟨x,h⟩ := quotDecomp xcc
        aesop_cat
   }
  homEquiv_unit := sorry -- : ∀ {X Y f}, (homEquiv X Y) f = (unit : _ ⟶ _).app X ≫ G.map f := by aesop_cat
  homEquiv_counit := sorry --  : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by aesop_cat


end adjunctionCC

end AdjCC


end CategoryTheory
