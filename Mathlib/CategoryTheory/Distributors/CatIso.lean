import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Category.Cat

open CategoryTheory

universe v₂ v₃ u₂ u₃
variable (B : Type u₂ ) [Category.{v₂} B]
variable (C : Type u₃ ) [Category.{v₃} C]

structure IsoOfCategory : Type (max u₂ u₃ v₂ v₃) where
  /-- The forward direction of a cat isomorphism. -/
  hom : B ⥤ C
  /-- The backwards direction of a cat isomorphism. -/
  inv : C ⥤ B
  /-- Composition of the two directions of a cat isomorphism is the identity functor
   on the source. -/
  hom_inv_id : hom ⋙ inv = 𝟭 B := by aesop_cat
  /-- Composition of the two directions of a cat isomorphism in reverse order
  is the identity functor on the target. -/
  inv_hom_id : inv ⋙ hom = 𝟭 C := by aesop_cat

def IsoOfCategory.symm (i : IsoOfCategory B C) : IsoOfCategory C B where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.inv_hom_id
  inv_hom_id := i.hom_inv_id

variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

def Functor.obj : ( B ⥤ C) → B → C := fun q => Prefunctor.obj (Functor.toPrefunctor (q : B ⥤ C))
def Functormap  {x y : B} (f : x ⟶ y ) (F : B ⥤ C) := F.map f

def inv_hom_idobj (i : IsoOfCategory B C )  : ∀ (a : B), i.inv.obj (i.hom.obj a) = a :=
  congrFun (congrArg Functor.obj i.hom_inv_id)

def hom_inv_idobj (i : IsoOfCategory B C ) : ∀ (a : C), i.hom.obj (i.inv.obj a) = a  :=
   congrFun (congrArg Functor.obj i.inv_hom_id)

def isoobj (i : IsoOfCategory B C) : B ≃ C where
  toFun := i.hom.obj
  invFun := i.inv.obj
  left_inv := inv_hom_idobj i
  right_inv := hom_inv_idobj i


def idFunctorMap {hom : B ⥤ C}{inv : C ⥤ B} (e : inv ⋙ hom = 𝟭 C)
  {x y : C}  (m m' : x ⟶ y)
  (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) : m = m' :=
    have h₁ :  m  = _ := Functor.congr_hom e.symm m
    have h₂ :  m' = _ := Functor.congr_hom e.symm m'
    h₁.trans (h ▸ h₂.symm)

-- theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]

-- -- on ne peut meme pas exprimer la meme chose pour les morphismes
-- def pb (hom : B ⥤ C) (inv : C ⥤ B) {x y : B} (f : x ⟶ y)
--     (hom_inv_id : hom ⋙ inv = 𝟭 B)  : (hom ⋙ inv).map f  = (𝟭 B).map f := sorry



-- def isoOfCategoryToEquivMorphisms (i : IsoOfCategory B C)
--     : (Σ x y : B, (x ⟶ y ))  ≃  (Σ x y : C, (x ⟶ y)) where
--   toFun := fun  ⟨x,y,f⟩ => ⟨i.hom.obj x, i.hom.obj y, i.hom.map f⟩ --  sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry


-- def isoOfCategoryToEquivMorphisms (i : IsoOfCategory B C)
--   (b : B ) (c : C) : ( b ⟶ i.inv.obj c)  ≃ (i.hom.obj b ⟶ c) where


-- def isoOfCategoryToEquivMorphisms (i : IsoOfCategory B C)
--   (x y : B ) : ( x ⟶ y)  ≃ (i.hom.obj x ⟶ i.hom.obj y) where
--   toFun := i.hom.map
--   invFun f := have e x : i.inv.obj (i.hom.obj x) = x := (isoobj i).left_inv x
--     eqToHom (e x).symm ≫ i.inv.map f ≫ eqToHom (e y)
--   left_inv := fun f =>
--       have r : let_fun e := fun x => (isoobj i).left_inv x
--                eqToHom (e x).symm ≫ i.inv.map (i.hom.map f) ≫ eqToHom (e y)  = f := by
--         have qq : i.inv.map (i.hom.map f) = (i.hom ⋙ i.inv).map f := by simp_all only [Functor.comp_map]
--         rw [qq]

--         let idfctr : i.hom ⋙ i.inv = 𝟭 B := i.hom_inv_id
--         let pb : (i.hom ⋙ i.inv).map f  = (𝟭 B).map f := sorry

--         have rs : eqToHom ((isoobj i).left_inv x).symm ≫ i.inv.map (i.hom.map f) ≫ eqToHom ((isoobj i).left_inv y) = f := by

--           sorry
--         exact rs
--       r
--   right_inv := congrFun (congrArg Functor.obj i.inv_hom_id)


-- --def IsoOfCategory_is_catiso : IsoOfCategory B C ≃ Iso (Cat.of B) (Cat.of C) := sorry --universe pb
