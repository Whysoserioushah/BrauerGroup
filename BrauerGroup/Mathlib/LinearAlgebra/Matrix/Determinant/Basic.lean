module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

-- TODO: Replace `det_zero`
@[simp] lemma det_zero' [Nonempty n] : (0 : Matrix n n R).det = 0 := det_zero ‹_›

end Matrix
