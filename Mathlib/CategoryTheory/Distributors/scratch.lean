def Item := Dynamic

def getValue (α : Type) [TypeName α] (values: List Item): List α :=
  values.filterMap (·.get? α)

deriving instance TypeName for String
deriving instance TypeName for Nat
deriving instance TypeName for Float

#eval getValue String [.mk "hi", .mk "there", .mk 2, .mk 4.5]  -- ["hi", "there"]
#eval getValue Nat [.mk "hi", .mk "there", .mk 2, .mk 4.5] -- [2]
#eval getValue Float [.mk "hi", .mk "there", .mk 2, .mk 4.5] -- [4.500000]
