module

public import Mathlib.RingTheory.NonUnitalSubring.Defs

@[expose] public section

variable {R : Type*} [NonUnitalRing R]

@[simp] lemma NonUnitalSubring.carrier_eq_coe (S : NonUnitalSubring R) : S.carrier = S := rfl
