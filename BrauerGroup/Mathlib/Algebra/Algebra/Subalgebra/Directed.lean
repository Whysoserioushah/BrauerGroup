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

/-- Every commutative subalgebra is contained in a maximal commutative subalgebra. -/
lemma Subalgebra.exists_le_maximal_isMulCommutative {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (M : Subalgebra R A) [IsMulCommutative M] :
    ∃ (L : Subalgebra R A), M ≤ L ∧ Maximal (fun S : Subalgebra R A ↦ IsMulCommutative S) L := by
  simp_rw +singlePass [← Set.mem_ofPred (α := Subalgebra R A) (p := fun S ↦ IsMulCommutative S)]
  refine zorn_le_nonempty₀ (s := {S : Subalgebra R A | IsMulCommutative S})
    (fun K hK1 hK2 y hy ↦ ?_) _ (by simpa)
  simp only [Set.mem_ofPred_eq]
  have : Nonempty K := ⟨⟨y, hy⟩⟩
  have : ∀ i : K, IsMulCommutative (i : Subalgebra R A) := fun i ↦ hK1 i.property
  exact ⟨⨆ i : K, (i : Subalgebra R A),
    Subalgebra.isMulCommutative_iSup hK2.directedOn.directed_val,
    fun z hz ↦ le_iSup (fun i : K ↦ (i : Subalgebra R A)) ⟨z, hz⟩⟩
