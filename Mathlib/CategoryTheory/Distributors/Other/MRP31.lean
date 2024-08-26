import Mathlib

open CategoryTheory Limits
noncomputable example (C D : Type*) [Category C] [Category D] (E : C ≌ D)
    (X : C) (hX : IsTerminal X) : IsTerminal (E.functor.obj X) :=
  IsTerminal.isTerminalObj E.functor X hX -- found with exact?

-- set_option trace.Meta.synthInstance true
variable (C D : Type*) [Category C] [Category D]
variable (E : C ≌ D)

-- set_option diagnostics true
noncomputable example : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) E.functor :=
  inferInstance


#min_imports
