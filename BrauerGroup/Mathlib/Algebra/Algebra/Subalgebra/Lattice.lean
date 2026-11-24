module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

@[expose] public section

lemma Subalgebra.map_centralizer_le_centralizer_image (s : Set A) (f : A →ₐ[R] B) :
    (centralizer _ s).map f ≤ centralizer _ (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  dsimp only [RingHom.coe_coe]
  rw [← map_mul, ← map_mul, hg h hh]

section

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]

lemma Subalgebra.le_centralizer_iff_isMulCommutative (L : Subalgebra k A) :
    L ≤ Subalgebra.centralizer k (L : Set A) ↔ IsMulCommutative L :=
  ⟨fun h ↦ ⟨⟨fun x y ↦ Subtype.ext <| h y.property x x.property⟩⟩,
    fun _ x hx y hy ↦ congrArg Subtype.val <| mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

/-- Adjoining an element of the centralizer of a commutative subalgebra `L` to `L` yields a
commutative subalgebra. -/
lemma Subalgebra.isMulCommutative_adjoin_insert_of_mem_centralizer {L : Subalgebra k A} {a : A}
    (ha : a ∈ Subalgebra.centralizer k (L : Set A)) [IsMulCommutative L] :
    IsMulCommutative (Algebra.adjoin k (insert a (L : Set A))) :=
  Algebra.isMulCommutative_adjoin k <| by
    rintro x (rfl | hx) y (rfl | hy) -
    · exact .refl _
    · exact ((Subalgebra.mem_centralizer_iff k).1 ha y hy).symm
    · exact (Subalgebra.mem_centralizer_iff k).1 ha x hx
    · exact congrArg Subtype.val <| mul_comm' (⟨x, hx⟩ : L) ⟨y, hy⟩

/-- A commutative subalgebra containing `L` centralizes `L`. -/
lemma Subalgebra.le_centralizer_of_le {L L' : Subalgebra k A} [IsMulCommutative L']
    (h : L ≤ L') : L' ≤ Subalgebra.centralizer k (L : Set A) :=
  fun x hx ↦ (Subalgebra.mem_centralizer_iff k).2
    fun y hy ↦ congrArg Subtype.val <| mul_comm' (⟨y, h hy⟩ : L') ⟨x, hx⟩

lemma Subalgebra.maximal_comm_iff_self_centralizer (L : Subalgebra k A) :
    Maximal (fun S : Subalgebra k A ↦ IsMulCommutative S) L ↔
      Subalgebra.centralizer k L = L := by
  refine ⟨fun ⟨hL1, hL2⟩ ↦ ?_, fun hL ↦ ?_⟩
  · refine le_antisymm (fun a ha ↦ ?_) ((le_centralizer_iff_isMulCommutative L).2 hL1)
    exact hL2 (isMulCommutative_adjoin_insert_of_mem_centralizer ha)
      (fun x hx ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem a hx))
      (Algebra.subset_adjoin (Set.mem_insert a _))
  · exact ⟨(le_centralizer_iff_isMulCommutative L).1 hL.ge,
      fun L' hL' hLL' ↦ (le_centralizer_of_le hLL').trans hL.le⟩

end
