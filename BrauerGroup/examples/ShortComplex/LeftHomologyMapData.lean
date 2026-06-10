import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

universe v u

open CategoryTheory

variable (R : Type u) [CommRing R] (S₁ : ShortComplex (ModuleCat.{v} R))
  (S₂ : ShortComplex (ModuleCat R)) (f : S₁ ⟶ S₂)

abbrev φK : ↥(LinearMap.ker (ModuleCat.Hom.hom S₁.g)) →ₗ[R]
    ↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) :=
  LinearMap.restrict f.2.hom
    fun x hx ↦ by
      have := (LinearMap.ext_iff.1 <| ModuleCat.hom_ext_iff|>.1 f.5) x
      simp at hx
      simp [hx] at this
      simp [this]

abbrev φH :
    ModuleCat.of R (LinearMap.ker (ModuleCat.Hom.hom S₁.g) ⧸ LinearMap.range S₁.moduleCatToCycles) ⟶
      .of R (↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ (φK _ _ _ f) fun ⟨x, hx1⟩ ⟨y, hy⟩ ↦ by
    simp [φK]
    simp_rw [Subtype.ext_iff] at hy ⊢
    simp at hy⊢
    rw [← hy]
    change ∃ y', _ = ModuleCat.Hom.hom _ (ModuleCat.Hom.hom S₁.f _)
    simp_rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    rw [← f.4]
    simp

@[simps]
def LeftHomologyMapData.ofModuleCat :
    ShortComplex.LeftHomologyMapData f
    (ShortComplex.moduleCatLeftHomologyData S₁)
    (ShortComplex.moduleCatLeftHomologyData S₂) where
  φK := ModuleCat.ofHom <| φK R S₁ S₂ f
  φH := φH R S₁ S₂ f
  commi := ModuleCat.hom_ext <| LinearMap.ext fun ⟨x, hx⟩ ↦ rfl
  commf' := ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
    change φK R S₁ S₂ f (S₁.moduleCatToCycles x) = S₂.moduleCatToCycles (f.τ₁ x)
    ext
    have h := LinearMap.ext_iff.1 ((ModuleCat.hom_ext_iff.1 f.comm₁₂).symm) x
    simpa [φK, ShortComplex.moduleCatToCycles] using h
  commπ := ModuleCat.hom_ext <| LinearMap.ext fun ⟨x, hx⟩ ↦ rfl

def ShortComplex.IsQuasiIsoAt_iff_moduleCat :
    ShortComplex.QuasiIso f ↔
      (∀ a : S₁.X₂, ModuleCat.Hom.hom S₁.g a = 0 →
        ∀ x : S₂.X₁, ConcreteCategory.hom S₂.f x = ModuleCat.Hom.hom f.τ₂ a →
        ∃ y, ConcreteCategory.hom S₁.f y = a) ∧
      ∀ a : S₂.X₂, ModuleCat.Hom.hom S₂.g a = 0 →
        ∃ a_1, ModuleCat.Hom.hom S₁.g a_1 = 0 ∧
        ∃ y, ConcreteCategory.hom S₂.f y = ModuleCat.Hom.hom f.τ₂ a_1 - a := by
  have hcomap : S₁.moduleCatToCycles.range ≤
      Submodule.comap (φK R S₁ S₂ f) S₂.moduleCatToCycles.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f.τ₁ x, ?_⟩
    ext
    have h := LinearMap.ext_iff.1 ((ModuleCat.hom_ext_iff.1 f.comm₁₂).symm) x
    simpa [φK, ShortComplex.moduleCatToCycles] using h.symm
  rw [ShortComplex.LeftHomologyMapData.quasiIso_iff (LeftHomologyMapData.ofModuleCat R S₁ S₂ f)]
  rw [ConcreteCategory.isIso_iff_bijective, Function.Bijective]
  congr!
  · rw [injective_iff_map_eq_zero]
    constructor
    · intro hinj a ha x hx
      have hzero : (ConcreteCategory.hom (LeftHomologyMapData.ofModuleCat R S₁ S₂ f).φH)
          (Submodule.Quotient.mk ⟨a, ha⟩) = 0 := by
        change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f) hcomap)
          (Submodule.Quotient.mk ⟨a, ha⟩) = 0
        rw [Submodule.mapQ_apply]
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨x, by ext; simpa [φK] using hx⟩
      have hz := hinj _ hzero
      have hzmem := (Submodule.Quotient.mk_eq_zero S₁.moduleCatToCycles.range).1 hz
      rcases hzmem with ⟨y, hy⟩
      use y
      have hy' := congrArg Subtype.val hy
      simpa using hy'
    · intro h q
      refine Submodule.Quotient.induction_on S₁.moduleCatToCycles.range q ?_
      intro z hq
      rcases z with ⟨a, ha⟩
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f) hcomap)
          (Submodule.Quotient.mk ⟨a, ha⟩) = 0 at hq
      rw [Submodule.mapQ_apply] at hq
      have hzmem := (Submodule.Quotient.mk_eq_zero S₂.moduleCatToCycles.range).1 hq
      rcases hzmem with ⟨x, hx⟩
      have ⟨y, hy⟩ := h a ha x (by
        have hx' := congrArg Subtype.val hx
        simpa [φK] using hx')
      apply (Submodule.Quotient.mk_eq_zero S₁.moduleCatToCycles.range).2
      exact ⟨y, by ext; simpa using hy⟩
  · constructor
    · intro hsurj a ha
      rcases hsurj (Submodule.Quotient.mk ⟨a, ha⟩) with ⟨q, hq⟩
      revert hq
      refine Submodule.Quotient.induction_on S₁.moduleCatToCycles.range q ?_
      intro z hq
      rcases z with ⟨a₁, ha₁⟩
      use a₁, ha₁
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f) hcomap)
          (Submodule.Quotient.mk ⟨a₁, ha₁⟩) = Submodule.Quotient.mk ⟨a, ha⟩ at hq
      rw [Submodule.mapQ_apply] at hq
      have hmem := (Submodule.Quotient.eq S₂.moduleCatToCycles.range).1 hq
      rcases hmem with ⟨y, hy⟩
      use y
      have hy' := congrArg Subtype.val hy
      simpa [φK] using hy'
    · intro hsurj q
      refine Submodule.Quotient.induction_on S₂.moduleCatToCycles.range q ?_
      intro z
      rcases z with ⟨a, ha⟩
      rcases hsurj a ha with ⟨a₁, ha₁, y, hy⟩
      refine ⟨Submodule.Quotient.mk ⟨a₁, ha₁⟩, ?_⟩
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f) hcomap)
          (Submodule.Quotient.mk ⟨a₁, ha₁⟩) = Submodule.Quotient.mk ⟨a, ha⟩
      rw [Submodule.mapQ_apply]
      apply (Submodule.Quotient.eq S₂.moduleCatToCycles.range).2
      exact ⟨y, by ext; simpa [φK] using hy⟩

  -- ShortComplex.LeftHomologyMapData.quasiIso_iff
  --   (LeftHomologyMapData.ofModuleCat R S₁ S₂ f)|>.2 <| by
  --   rw [ConcreteCategory.isIso_iff_bijective]
  --   refine ⟨?_, sorry⟩
  --   rw [injective_iff_map_eq_zero]
  --   rintro x hx
  --   obtain ⟨⟨x, hx1⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  --   simp [Subtype.ext_iff] at hx
  --   simp [Subtype.ext_iff]
    -- obtain ⟨⟨x2, hx2⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    -- simp [Submodule.Quotient.eq] at h12
