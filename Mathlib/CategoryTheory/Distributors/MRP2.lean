import Mathlib.CategoryTheory.Category.Cat

namespace CategoryTheory

universe v u
variable (B: Cat.{u,u})

def one_Bop_asfctr  := (𝟙 (Bᵒᵖ) : Bᵒᵖ ⥤ Bᵒᵖ )


def id_B  := (𝟭 B : B ⥤ B )

def one_B   := (𝟙 B : B ⟶ B )

def one_B_asfctr   := (𝟙 B : B ⥤ B )


def id_Bop    := (𝟭 (Bᵒᵖ) : Bᵒᵖ ⥤ Bᵒᵖ )

def one_Bop  := (𝟙 (Bᵒᵖ) : Bᵒᵖ ⟶ Bᵒᵖ )


def one_Bop_asfctr  := (𝟙 (Bᵒᵖ) : Bᵒᵖ ⥤ Bᵒᵖ )


def one_Bop_asfctr  := ((𝟙 (Bᵒᵖ) : Bᵒᵖ ⟶ Bᵒᵖ) : CategoryTheory.Functor.{u,u,u,u} Bᵒᵖ Bᵒᵖ )

section other

variable (B: Cat.{u,u})

def one_Bop_asfctr  := ((𝟙 (Bᵒᵖ) : Bᵒᵖ ⟶ Bᵒᵖ) : CategoryTheory.Functor.{u,u,u,u} Bᵒᵖ Bᵒᵖ )

end other

end CategoryTheory
