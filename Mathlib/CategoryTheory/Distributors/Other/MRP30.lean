universe u
variable {B : Type u }

abbrev Simple (B : Type u ) :=  Σ x : B, Bool

def id' (th : Simple B ) : Simple B := ⟨th.fst, true⟩

def isOK (th : Simple B) : True := by
      let th' := id' th
      let t' := th'.fst
      have : th.fst =  t' := rfl
      simp

def isKO (th : Simple B) : True := by
      let ⟨t', _⟩ := id' th
      have : th.fst =  t' := rfl
-- type mismatch
--   rfl
-- has type
--   th.fst = th.fst : Prop
-- but is expected to have type
--   th.fst = t' : Prop
      simp
