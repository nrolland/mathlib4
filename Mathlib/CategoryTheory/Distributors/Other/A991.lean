import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Distributors.CatIso

open CategoryTheory
open Limits
open IsLimit

universe v₁ v₂ v₃ vm u₁ u₂ u₃ u um
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂ } [Category.{v₂} B]
variable {C : Type u₂ } [Category.{v₂} C]

variable (F G : J ⥤ B)


abbrev Terminal (B : Type u₂ ) [Category.{v₂} B] :=  Σ x : B, IsTerminal x

def FunctorEqToMapHEq  {F G : B ⥤ C} (h: F = G)  {x y : B} (f : x ⟶ y) : HEq (F.map f) (G.map f) :=
  by subst h;exact HEq.refl _

def idFunctorMap {hom : B ⥤ C}{inv : C ⥤ B} (e :  𝟭 C = (inv ⋙ hom ) )
  {x y : C}  (m m' : x ⟶ y)
  (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) : m = m' :=
    have as1 : HEq m ((𝟭 C).map m)  := heq_of_eq (Functor.id_map _).symm
    have as2 : HEq ((𝟭 C).map m) ((inv ⋙ hom).map m) := FunctorEqToMapHEq e m
    have as3 : HEq ((inv ⋙ hom).map m) ((inv ⋙ hom).map m') := heq_of_eq h
    have as4 : HEq ((inv ⋙ hom).map m') ((𝟭 C).map m') := (FunctorEqToMapHEq e m').symm
    have as5 : HEq  ((𝟭 C).map m')  m' := heq_of_eq (Functor.id_map _)
    have as : HEq m m' := as1.trans (as2.trans  (as3.trans  (as4.trans as5 ) ) )
    eq_of_heq as


instance terminalGroupoid : Groupoid (Terminal B) where
  Hom x y  :=  x.1 ⟶ y.1
  id x := 𝟙 x.1
  comp {x y z} f g :=  f ≫ g
  inv {x y} _  :=  IsTerminal.from x.2 y.1
  inv_comp {_ y} _ := IsTerminal.hom_ext y.2 _ _
  comp_inv {x _} _ := IsTerminal.hom_ext x.2 _ _
def terminalConnected (x y : Terminal B) : x ⟶ y := Limits.IsTerminal.from y.2 x.1


def asEmptyConeMorphism {x y : C} (f : x ⟶ y) :
    Limits.ConeMorphism (Limits.asEmptyCone x) (Limits.asEmptyCone y) :=
    { hom := f }

theorem uniq_morphism_to_terminal {s t : B} (h : IsTerminal t) {f f' : s ⟶ t} : f = f' :=
  congrArg ConeMorphism.hom (uniq_cone_morphism h : asEmptyConeMorphism f = asEmptyConeMorphism f')


def toNewTerminal {i:  IsoOfCategory B C} {t : B} (h : IsTerminal t)  x :=
  let eqtohom := x |> (isoobj i).right_inv |> Eq.symm |> eqToHom
  eqtohom ≫ i.hom.map (h.from (i.inv.obj x ))


def isoOfCategoryIsoTerminal (i:  IsoOfCategory B C)
  (t : B) (h : IsTerminal t) : IsTerminal (i.hom.obj t) :=
  IsTerminal.ofUniqueHom (toNewTerminal h)
  (fun x (m : x ⟶ i.hom.obj t) =>
    let eqtohom2  := t |> (isoobj i).left_inv |> eqToHom

    let toNewTerminal' :=  i.inv.map (toNewTerminal h x) ≫ eqtohom2
    let m' :=  i.inv.map m ≫ eqtohom2

    have : m' = toNewTerminal' := uniq_morphism_to_terminal h
    have eq : i.hom.map m' = i.hom.map toNewTerminal'  :=  congrArg i.hom.map this

    have eq : i.hom.map m' = i.hom.map toNewTerminal'  :=  congrArg i.hom.map this

    have : m = toNewTerminal h x := sorry
    -- have res : m = i.hom.map (toNewTerminal' ) := sorry
    -- by simp
    sorry)



def isoOfCategoryIsoTerminalqw (i:  IsoOfCategory B C)
  (t : B) (h : IsTerminal t) : IsTerminal (i.hom.obj t) :=
  IsTerminal.ofUniqueHom (toNewTerminal h)
  (fun x (m : x ⟶ i.hom.obj t) => -- on veut : m = toNewTerminal h x, dans C

    let eq2 : (isoobj i).invFun ((isoobj i).toFun t) ⟶ t  := t |> (isoobj i).left_inv |> eqToHom

    -- on a :  inv m = inv (toNewTerminal h x), dans B
    let toNewTerminal' :=  i.inv.map (toNewTerminal h x) ≫ eq2
    let m' :=  i.inv.map m ≫ eq2
    have uniq : m' = toNewTerminal' := uniq_morphism_to_terminal h

    -- on a :  (hom ⋙ inv).map m = (hom ⋙ inv).map (toNewTerminal h x), dans B
    have eq : i.hom.map m' = i.hom.map toNewTerminal'  :=  congrArg i.hom.map uniq

    -- on veut appliquer (hom ⋙ inv) = 𝟙 B
    -- plus precisement on veut appliquer (hom ⋙ inv).map _ = (𝟙 B).map _

    -- mais F = G => HEq (F.map f) (G.map f)
    -- donc on obtient HEq ((hom ⋙ inv).map m) ((𝟙 B).map m)
    -- donc on obtient HEq ((hom ⋙ inv).map (toNewTerminal h x)) ((𝟙 B).map (toNewTerminal h x))
    -- on a aussi HEq ((hom ⋙ inv).map m) ((hom ⋙ inv).map (toNewTerminal h x))
    -- donc on a HEq ((𝟙 B).map m) ((𝟙 B).map (toNewTerminal h x))
    -- donc on a HEq m (toNewTerminal h x)
    -- ils sont du meme type, donc egalite

    have : m = toNewTerminal h x := sorry
    sorry)


def thepb (i:  IsoOfCategory B C) (x : C) (t : B )(m m' : x ⟶ i.hom.obj t)
    (h : i.hom.map (i.inv.map m  ≫ ( t |> (isoobj i).left_inv |> eqToHom)) =
         i.hom.map (i.inv.map m' ≫ ( t |> (isoobj i).left_inv |> eqToHom))) : (m = m') := sorry

def thepb2 (i:  IsoOfCategory B C) (x : C) (t : B )(m m' : x ⟶ i.hom.obj t)
    (h : i.hom.map (i.inv.map m  ) =
         i.hom.map (i.inv.map m' )) : (m = m') := sorry

def mapF  {x y : B} (f : x ⟶ y) (F : B ⥤ C) := F.map f

def aSol (inv : C ⥤ B) (hom : B ⥤ C) (e : (inv ⋙ hom ) = 𝟭 C)
  {x : C} {t : B } (m m' : x ⟶ hom.obj t)
  (h : ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m')) : (m = m') :=
  idFunctorMap e.symm m m' h

def aPb (inv : C ⥤ B) (hom : B ⥤ C) (e : 𝟭 C = (inv ⋙ hom ) )
  {x y : C}  (m m' : x ⟶ y)
  (h :  ((inv ⋙ hom ).map m) = ((inv ⋙ hom).map m') ) :  m = m' :=
    idFunctorMap e m m' h
