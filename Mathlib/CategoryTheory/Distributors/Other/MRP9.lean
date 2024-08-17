import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Types
set_option linter.longLine false

namespace CategoryTheory
open Limits
universe v u

section Question1
    variable (A : Type) [Category A]
    variable (P : A ⥤ Type u) --- u
    def OK : HasColimit P := inferInstance

    variable (A : Type) [Category A]
    variable (P : A ⥤ Type)
    def OKalso : HasColimit P := inferInstance

    variable (A : Type (u+1)) [Category A] -- u+1
    variable (P : A ⥤ Type u)
    def sad : HasColimit P := inferInstance ---- failed to synthesize Limits.HasColimit QfromCat

    variable (A : Type u) [Category A]
    variable (P : A ⥤ Type*) -- *
    def sadalso : HasColimit P := inferInstance -- failed to synthesize Limits.HasColimit QfromCat

    variable (A : Type*) [Category A] -- *
    variable (P : A ⥤ Type)
    def sadalsoagain : HasColimit P := inferInstance -- failed to synthesize Limits.HasColimit QfromCat
end Question1


section Question2
    variable (C :  Cat)
    variable (QfromCat : C ⥤ Type u)
    def happy := colimit QfromCat

    #synth HasColimit QfromCat  -- ok
    #check Types.hasColimit QfromCat -- ok
    def sadagain : HasColimit QfromCat := Types.hasColimit QfromCat -- failed to synthesize Limits.HasColimit QfromCat

    variable (C :  Cat.{v,u}) -- v
    variable (QfromCat : C ⥤ Type u)
    def ok : HasColimit QfromCat := Types.hasColimit QfromCat -- failed to synthesize Limits.HasColimit QfromCat
end Question2


section Question3
    variable (C :  Cat.{v,(u+0)})
    variable (A : Type) [Category A]
    variable (QfromCat : C ⥤ Type (u))

    def allright := colimit QfromCat  --failed to synthesize Limits.HasColimit Q

    variable (D :  Cat)
    variable (declaration_of_something_else_in_cat : D ⟶ Cat.of (Type (u)))

    def notanymore := colimit QfromCat  --failed to synthesize Limits.HasColimit Q
end Question3

end CategoryTheory
