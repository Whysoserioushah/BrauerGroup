module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed

@[expose] public section

namespace Subalgebra
variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {K : ι → Subalgebra R A}
  {s : Set ι} {x : A}

lemma coe_biSup_of_directedOn (hs : s.Nonempty) (dir : DirectedOn (K · ≤ K ·) s) :
    ↑(⨆ i ∈ s, K i) = ⨆ i ∈ s, (K i : Set A) := by
  have := hs.to_subtype
  rw [← iSup_subtype'', ← iSup_subtype'', coe_iSup_of_directed, Set.iSup_eq_iUnion]
  rwa [← Function.comp_def, directed_comp, ← directedOn_iff_directed]

lemma mem_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) K) : x ∈ iSup K ↔ ∃ i, x ∈ K i := by
  simpa using congr(x ∈ $(coe_iSup_of_directed dir))

end Subalgebra
