module

public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

@[expose] public section

variable {R : Type*} [NonUnitalSemiring R]

@[simp]
lemma NonUnitalSubsemiring.carrier_eq_coe (S : NonUnitalSubsemiring R) : S.carrier = S := rfl
