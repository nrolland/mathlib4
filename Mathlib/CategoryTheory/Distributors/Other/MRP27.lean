/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Distributors.End
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

--- distributors
universe u
variable {A : Type u } [Category.{u} A]
variable {B : Type u } [Category.{u} B]
variable {C : Type u } [Category.{u} C]
variable {D : Type u } [Category.{u} D]

def plugOne : (B × D)ᵒᵖ  × (A × C) ⥤ (Bᵒᵖ × A) × Dᵒᵖ × C  := Functor.prod ((prodOpEquiv B).functor) (𝟭 _) ⋙ prod.associator _ _ _ ⋙ Functor.prod (𝟭 _)  (prod.inverseAssociator  _ _ _ ) ⋙    Functor.prod (𝟭 _) (Functor.prod (Prod.swap _ _) (𝟭 _) ) ⋙     Functor.prod (𝟭 _) (prod.associator _ _ _) ⋙    (prod.inverseAssociator  _ _ _ )
def plugTwo   : (Cᵒᵖ × A) × (Bᵒᵖ × B) ⥤  (B × C)ᵒᵖ × (A × B)  := (prod.inverseAssociator  _ _ _ ) ⋙ Functor.prod (Prod.swap _ _) (𝟭 _) ⋙ Functor.prod (prod.inverseAssociator _ _ _) (𝟭 _) ⋙ (prod.associator  _ _ _ ) ⋙ Functor.prod ((prodOpEquiv B).inverse) (𝟭 _)

def timesObj (P : Dist.{u} A B) (Q: Dist.{u} C D) :
    Dist.{u} (A × C) (B × D) :=
  plugOne ⋙ Functor.prod P Q ⋙ tensor (Type u)

def timesFunctor : (Dist.{u} A B) × ( Dist.{u} C D) ⥤
  Dist.{u} (A × C) (B × D)  where
  obj := fun (P,Q) ↦ timesObj P Q
  map := fun (a,b) ↦ whiskerLeft plugOne (whiskerRight (NatTrans.prod a b) (tensor (Type u)))

def opObj (P : Dist A B) : Dist Bᵒᵖ Aᵒᵖ := (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _) ⋙ P

def op : (Dist A B) ⥤ Dist Bᵒᵖ Aᵒᵖ where
  obj := opObj
  map := whiskerLeft (Functor.prod (unopUnop _) (𝟭 _) ⋙ Prod.swap _ _)

--- Composition

def compObj (P : Dist A B) (Q: Dist B C) : Dist A C  :=
  ((whiskeringRight _ _ _ ).obj myCoendPt).obj (curryObj (plugTwo ⋙ timesObj P Q))

def comp : (Dist.{u} A B) × (Dist.{u} B C) ⥤  Dist.{u} A C  :=
  timesFunctor ⋙ (whiskeringLeft _ _  _ ).obj plugTwo ⋙ curry ⋙ (whiskeringRight _ _ _ ).obj myCoendPt


--- Laws

def id  (B : Type u) [Category.{u} B] : Dist B B  := Functor.hom B

lemma comp_id (F : Dist A B) : comp.obj  (F, id B) = F := by
  Functor.hext
  sorry


end CategoryTheory.Distributors
