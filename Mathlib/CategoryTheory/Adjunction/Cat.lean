/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
/-!
# Adjunctions related to Cat, the category of categories

The embedding `typeToCat: Type ⥤ Cat`, mapping a type to the corresponding discrete category, is
left adjoint to the functor `Cat.objects`, which maps a category to its set of objects.



## Notes
All this could be made with 2-functors

## TODO

Define the left adjoint `Cat.connectedComponents`, which map
a category to its set of connected components.

-/

universe v u
namespace CategoryTheory

variable (X : Type u) (C : Cat)

private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun f x := f.obj ⟨x⟩
  invFun := Discrete.functor
  left_inv F := Functor.ext (fun _ ↦ rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)
  right_inv _ := rfl

private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

/-- `typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type` -/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects where
  homEquiv  := typeToCatObjectsAdjHomEquiv
  unit := { app:= fun _  ↦ Discrete.mk }
  counit := {
    app := typeToCatObjectsAdjCounitApp
    naturality := fun _ _ _  ↦  Functor.hext (fun _ ↦ rfl)
      (by intro ⟨_⟩ ⟨_⟩ f
          obtain rfl := Discrete.eq_of_hom f
          aesop_cat ) }


section AdjCC
section techniques
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

def fnToFctr : (connectedComponents.obj C ⟶ X) → (C ⥤ typeToCat.obj X) := fun fct =>
  { obj := fun x => x |> toCC |> fct |> Discrete.mk
    map := fun {a b} f => Discrete.eqToHom (congrArg fct (releqq f))
    map_id := by simp
    map_comp := by simp
  }


def fctrToFn :  (C ⥤ typeToCat.obj X) → (connectedComponents.obj C ⟶ X) := fun fctr  =>
  Quotient.lift (s:= (@catisSetoid C))
     (fun c => (fctr.obj c).as)
     (fun _ _ h => eq_of_zigzag X (transportZigzag fctr h))

set_option linter.longLine false

private def linverse' : Function.LeftInverse (fctrToFn X C ) (fnToFctr X C ) :=
  fun (f : connectedComponents.obj C ⟶ X) => by
    funext xcc
    obtain ⟨x,h⟩ := quotDecomp xcc
    calc
      fctrToFn X C (fnToFctr X C f) xcc =  fctrToFn X C (fnToFctr X C f) ⟦x⟧ := by rw [<- h]
      _  = ((fnToFctr X C f).obj x).as := rfl
      _  = f ⟦x⟧ := rfl
      _  = f xcc := by rw [h]

private def rinverse' : Function.RightInverse (fctrToFn X C ) (fnToFctr X C ) :=
  fun (fctr : C ⥤ (typeToCat.obj X)) => by
    fapply Functor.hext
    · intro c; rfl
    · intro c d f
      have cdeq : fctr.obj c = fctr.obj d := f |> fctr.map |> Discrete.eq_of_hom |> congrArg Discrete.mk
      let ident : (discreteCategory X).Hom (fctr.obj c) (fctr.obj d) := by rw [cdeq]; exact 𝟙 _
      let p := Subsingleton.helim rfl ident ((fnToFctr X C (fctrToFn X C fctr)).map f)
      exact (p.symm).trans (Subsingleton.helim rfl ident (fctr.map f) : HEq ident (fctr.map f))




def isadj_CC_TypeToCat : connectedComponents ⊣ typeToCat where
  homEquiv  := fun C X  ↦ {
    toFun := fnToFctr X C
    invFun  := fctrToFn X C
    left_inv  := linverse' X C
    right_inv  := rinverse' X C
    }
  unit : 𝟭 Cat ⟶ connectedComponents ⋙ typeToCat := { app:= fun C  ↦ fnToFctr _ _ (𝟙 (ccSet C)) }
  counit : typeToCat ⋙ connectedComponents ⟶ 𝟭 (Type u) :=  {
      app := fun X => fctrToFn X (typeToCat.obj X) (𝟙 (typeToCat.obj X) : typeToCat.obj X ⥤ typeToCat.obj X)
      naturality := fun X Y f => by
        funext xcc
        obtain ⟨x,h⟩ := quotDecomp xcc
        aesop_cat
   }
  homEquiv_unit := fun {C X h} => Functor.hext (fun _ => by rfl) (fun _ _ _ => by rfl)
  homEquiv_counit := fun {C X G} => by funext cc;obtain ⟨_,_⟩ := quotDecomp cc; aesop_cat


end adjunctionCC

end AdjCC


end CategoryTheory
