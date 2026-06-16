module

public import BrauerGroup.Subfield.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace SubField
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {L : SubField K A}

instance [FiniteDimensional K A] : FiniteDimensional K L := .finiteDimensional_subalgebra L.1

end SubField
