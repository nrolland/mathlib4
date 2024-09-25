Definitional equality is "special" to prove things in lean :

Form some type T(\alpha) and T(\beta) on top of definitionally equal type \alpha and \beta, one can still talk about equality among some elements x \in T(\alpha) and y \in T(\beta). It's not a type error.

If \alpha and \beta are not definitionally equal, such equality is a type error, and one has to resort to heterogeneous equality.

Could one have *bounded* definitional equality : under some typeclass representing (non definitional) equality of types \alpha and \beta, add such equality to the rules at play for definitional equality.

This would not lead to contradiction because the values produced are only acessible if one proves the required equality.
Using this bounded definitional equality would more closely related to intuition about two terms being definitianly equal of they have the same definition (cf end of example)

This is loosely similar to [implicit configuration](https://okmij.org/ftp/Haskell/tr-15-04.pdf) from Oleg Kiselyov where some runtime value provided at the start of a program is reflected as static value.

What would be needed to use such a system is a way to reflect (subset of?) proofs of non definitional equalities to typeclass instances.

Here's an example using category theory


```lean4
import Mathlib.CategoryTheory.Functor.Const

open CategoryTheory
open Functor

universe v₁ vm u₁ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {M : Type um } [Category.{vm} M]
variable {F G H: J ⥤ M}

-- Simple simply wraps M
structure Simple (F : J ⥤ M) where  pt : M

structure SimpleMorphism  {F : J ⥤ M} (x y : Simple F) where  hom : x.pt ⟶ y.pt
instance  simple (F : J ⥤ M) : Category (Simple F) where
  Hom x y:=  SimpleMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

-- We can shift from Simple F to Simple G
def simpleCompose  (α : F ⟶ G) : Simple F ⥤ Simple G  where
  obj c :=  { pt := c.pt  }
  map {X Y} (m : X ⟶ Y) := { hom := m.hom }

-- Key part : definitional equality of types
example (α : F ⟶ G) (β : G ⟶ H) (x : Simple F):
    (((simpleCompose (α ≫ β)).obj x)) = ((simpleCompose α ⋙ simpleCompose β).obj x) :=
  rfl

-- That's not a type error although the dependant type `⟶` is called at different indices
example (α : F ⟶ G) (β : G ⟶ H) (x y: Simple F) :
    ((simpleCompose (α ≫ β)).obj x ⟶ (simpleCompose (α ≫ β)).obj y)
    = ((simpleCompose α ⋙ simpleCompose β).obj x ⟶ (simpleCompose α ⋙ simpleCompose β).obj y)
  := rfl


------------------------------------------------------------------------------------
@[ext]
structure MyCone  (F : J ⥤ M) where
  pt : M
  π : (const J).obj pt ⟶ F

structure MyConeMorphism   (x y : MyCone F) where
  hom : x.pt ⟶ y.pt

instance : Category (MyCone F) where
  Hom x y:=  MyConeMorphism x y
  id x := { hom := 𝟙 x.pt }
  comp f g := { hom := f.hom ≫ g.hom }

-- a shift from F to G modifies the object NOT definitionally
def pc (α : F ⟶ G) : MyCone F ⥤ MyCone G  where
  obj c :=  {pt := c.pt, π := c.π  ≫ α }
  map {X Y} m := { hom := m.hom }


-- Key part : This equality is NOT a definitional equality
example (α : F ⟶ G) (β : G ⟶ H) (x : MyCone F):
    (((pc (α ≫ β)).obj x)) =  ((pc α ⋙ pc β).obj x) :=
  MyCone.ext rfl (by simp;exact (Category.assoc _ _ _).symm)

-- Therefore we have a type mismatch
example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
    (pc (α ≫ β)).map m = (pc α ⋙ pc β).map m
  := sorry
--   (pc α ⋙ pc β).map m
-- has type
--   (pc α ⋙ pc β).obj x ⟶ (pc α ⋙ pc β).obj y : Type vm
-- but is expected to have type
--   (pc (α ≫ β)).obj x ⟶ (pc (α ≫ β)).obj y : Type vm


-- Key solution :  Instead of a type error, one would want a constraint and simply use definitional equality
-- Look at the definition of map. Both side have the same definition.
example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y)
  [TyEq ((pc α ⋙ pc β).obj x ⟶ (pc α ⋙ pc β).obj y) ((pc (α ≫ β)).obj x ⟶ (pc (α ≫ β)).obj y) ] :
  (pc (α ≫ β)).map m = (pc α ⋙ pc β).map m := bounded_rfl


-- Look at the definition of map. They are definitionally equal.
example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
  (pc (α ≫ β)).map m = { hom := m.hom }  := rfl

example (α : F ⟶ G) (β : G ⟶ H) (x y: MyCone F) (m : x ⟶ y) :
   (pc α ⋙ pc β).map m = { hom := m.hom }  := rfl
```
