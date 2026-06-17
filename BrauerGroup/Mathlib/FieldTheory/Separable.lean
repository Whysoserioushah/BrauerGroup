module

public import Mathlib.FieldTheory.Separable

public section

open Polynomial

variable {F K E : Type*} [Field F] [Field K] [Ring E] [Algebra F K] [Algebra F E] [Nontrivial E]
  {x : K}

-- TODO: Replace `IsSeparable.of_algHom`
lemma IsSeparable.of_algHom' (f : K →ₐ[F] E) (h : IsSeparable F (f x)) : IsSeparable F x := by
  have ⟨q, hq⟩ := minpoly.dvd F x (p := minpoly F (f x)) <| f.injective <| by
    simp [← aeval_algHom_apply]
  exact .of_mul_left <| by rwa [← hq]
