import BrauerGroup.FrobeniusTheorem

suppress_compilation

open Quaternion BrauerGroup TensorProduct

abbrev toEnd_map_aux (q1 q2 : ℍ[ℝ]) : Module.End ℝ ℍ[ℝ] where
    toFun x := q1 * x * (star q2)
    map_add' x1 x2 := by simp [mul_add, add_mul]
    map_smul' r x := by simp

abbrev toEnd_map_aux' (q1 : ℍ[ℝ]) : ℍ[ℝ] →ₗ[ℝ] Module.End ℝ ℍ[ℝ] where
  toFun q2 := toEnd_map_aux q1 q2
  map_add' x1 x2 := by ext : 1; simp [mul_add]
  map_smul' r x := by ext : 1; simp [Algebra.mul_smul_comm _ _ (star x)]

abbrev toEnd_map : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] →ₗ[ℝ] Module.End ℝ (ℍ[ℝ]) := TensorProduct.lift {
  toFun := fun q1 ↦ toEnd_map_aux' q1
  map_add' := fun x1 x3 ↦ by ext : 2; simp [add_mul]
  map_smul' := fun r x ↦ by ext : 2; simp
}

set_option maxSynthPendingDepth 2 in
lemma toEnd_map.map_mul (x1 x2 : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) : toEnd_map (x1 * x2) =
    toEnd_map x1 * toEnd_map x2 := by
  induction x1 using TensorProduct.induction_on with
  | zero => simp
  | tmul q1 q2 =>
    induction x2 using TensorProduct.induction_on with
    | zero => simp
    | tmul q3 q4 => ext : 1; simp [← _root_.mul_assoc]
    | add x y h1 h2 =>
      rw [mul_add, map_add, map_add, mul_add, h1, h2]
  | add x y h1 h2 => rw [add_mul, map_add, map_add, add_mul, h1, h2]

abbrev toEnd : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] →ₐ[ℝ] Module.End ℝ (ℍ[ℝ]) where
  toFun := toEnd_map
  map_one' := by ext : 1; simp [Algebra.TensorProduct.one_def]
  map_mul' := toEnd_map.map_mul
  map_zero' := rfl
  map_add' := toEnd_map.map_add
  commutes' r := by ext : 1; simp only [Algebra.TensorProduct.algebraMap_apply,
    algebraMap_def, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, star_one, _root_.mul_one,
    Module.algebraMap_end_apply]; exact coe_mul_eq_smul r _

instance : Algebra.IsCentral ℝ ℍ[ℝ] := ⟨fun q hq ↦ by
  rw [Subalgebra.mem_center_iff] at hq
  change ∃(_ : _), _ = _
  use q.1
  let eq1 := hq ⟨0, 1, 0, 0⟩
  let eq2 := hq ⟨0, 0, 1, 0⟩
  let eq3 := hq ⟨0, 0, 0, 1⟩
  rw [Quaternion.ext_iff] at eq1 eq2 eq3
  obtain ⟨_, _, eq13, eq14⟩ := eq1
  obtain ⟨_, eq22, _, eq24⟩ := eq2
  obtain ⟨_, eq32, eq33, _⟩ := eq3
  simp only [re_mul, zero_mul, _root_.one_mul, zero_sub, sub_zero, mul_zero, _root_.mul_one,
    imI_mul, zero_add, add_zero, imJ_mul, sub_self, imK_mul, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at *
  simp only [neg_eq_self, self_eq_neg, Algebra.ofId_apply, algebraMap_def] at *
  change (⟨q.1, 0, 0, 0⟩ : ℍ[ℝ]) = ⟨q.1, q.2,q.3,q.4⟩
  ext <;> simp_all⟩

instance : IsSimpleRing (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) := IsCentralSimple.TensorProduct.simple _ _ _

lemma toEnd_bij : Function.Bijective toEnd :=
  bijective_of_dim_eq_of_isCentralSimple ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) (Module.End ℝ ℍ[ℝ]) toEnd <| by
    rw [show Module.finrank ℝ (Module.End ℝ _) =
      Module.finrank ℝ (Matrix (Fin <| Module.finrank ℝ ℍ[ℝ]) (Fin <| Module.finrank ℝ ℍ[ℝ]) ℝ)
      from (algEquivMatrix <| Module.finBasis _ _).toLinearEquiv.finrank_eq]
    simp [Quaternion.finrank_eq_four, Fintype.card_fin, Module.finrank_matrix]

def QuaternionTensorEquivMatrix : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (AlgEquiv.ofBijective toEnd toEnd_bij).trans <| algEquivMatrix
    (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ))

lemma QuaternionTensorEquivOne : IsBrauerEquivalent (K := ℝ) ⟨.of ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ])⟩ ⟨.of ℝ ℝ⟩ :=
  ⟨1, 4, one_ne_zero, by omega, ⟨dim_one_iso _ |>.trans QuaternionTensorEquivMatrix⟩⟩

lemma QuaternionNotEquivR : ¬ IsBrauerEquivalent (K := ℝ) ⟨.of ℝ ℍ[ℝ]⟩ ⟨.of ℝ ℝ⟩ := by
  intro h
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  letI : NeZero n := ⟨hn⟩
  letI : NeZero m := ⟨hm⟩
  obtain ⟨e'⟩ := Wedderburn_Artin_uniqueness₀ ℝ (Matrix (Fin n) (Fin n) ℍ[ℝ])
    n m ℍ[ℝ] AlgEquiv.refl ℝ e
  have eq2 := e'.toLinearEquiv.finrank_eq
  simp only [Module.finrank_self] at eq2
  haveI := eq2.symm.trans <| Quaternion.finrank_eq_four (R := ℝ)
  norm_num at this

lemma BrauerOverR (A : CSA.{0, 0} ℝ) :
    IsBrauerEquivalent A ⟨.of ℝ ℝ⟩ ∨ IsBrauerEquivalent A ⟨.of ℝ ℍ[ℝ]⟩ := by
  if h : IsBrauerEquivalent A ⟨.of ℝ ℝ⟩ then left; assumption
  else
  right
  obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version.{0, 0} ℝ A
  letI := A.4
  letI : FiniteDimensional ℝ D := is_fin_dim_of_wdb ℝ A hn D e
  obtain ⟨⟨e'⟩⟩ | hD2 | hD3 := FrobeniusTheorem D
  · have := is_central_of_wdb ℝ A n D hn e|>.center_eq_bot
    have e2 : Subalgebra.center ℝ D ≠ ⊥ := by
      refine ne_of_gt ?_
      letI : Algebra ℂ D := RingHom.toAlgebra' e'.symm fun z d ↦ by
        simp only [RingHom.coe_coe]
        rw [← e'.symm_apply_apply d, ← map_mul, mul_comm, map_mul]
      letI : IsScalarTower ℝ ℂ D := {
        smul_assoc := fun r z d ↦ by
          change e'.symm _  * _ = _ • (e'.symm z * d)
          rw [map_smul, Algebra.smul_mul_assoc]
      }
      have : Subalgebra.center ℝ D = ⊤ := by
        apply le_antisymm (fun _ _ ↦ trivial) <| by
          rintro d -
          rw [Subalgebra.mem_center_iff]
          intro d'
          rw [← e'.symm_apply_apply d, ← e'.symm_apply_apply d']
          conv_lhs => rw [← _root_.map_mul e'.symm, mul_comm, map_mul]
      rw [this]
      exact SetLike.lt_iff_le_and_exists.2 ⟨fun _ _ ↦ ⟨⟩, ⟨e'.symm Complex.I, ⟨⟨⟩, by
        by_contra! mem
        change ∃(_ : _), _ = _ at mem
        obtain ⟨r, eq⟩ := mem
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at eq
        apply_fun e' at eq
        rw [e'.apply_symm_apply] at eq
        rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, map_smul, map_one] at eq
        simp only [Complex.real_smul, _root_.mul_one] at eq
        rw [Complex.ext_iff] at eq
        obtain ⟨_, fal⟩ := eq
        simp only [Complex.ofReal_im, Complex.I_im, zero_ne_one] at fal⟩⟩⟩
    tauto
  · have : IsBrauerEquivalent A ⟨.of ℝ ℝ⟩ :=
      ⟨1, n, one_ne_zero, hn, ⟨dim_one_iso A|>.trans <| e.trans hD2.some.mapMatrix⟩⟩
    tauto
  · exact ⟨1, n, one_ne_zero, hn, ⟨dim_one_iso A |>.trans <| e.trans hD3.some.mapMatrix⟩⟩

open scoped Classical in
abbrev toC2 : Additive (BrauerGroup ℝ) →+ ZMod 2 where
  toFun := Quotient.lift (fun A ↦ if h1 : IsBrauerEquivalent A (one_in')
    then 0 else 1) <|
    fun A B hAB ↦ by
      change IsBrauerEquivalent _ _ at hAB
      if h : IsBrauerEquivalent A (BrauerGroup.one_in') then
        simp [h, hAB.symm.trans h]
      else
        simp [h]
        have : ¬ IsBrauerEquivalent B (BrauerGroup.one_in') := by
          by_contra!
          haveI := hAB.trans this
          tauto
        simpa using this
  map_zero' := by
    change Quotient.lift _ _ (Quotient.mk'' (BrauerGroup.one_in')) = 0
    simp only [dite_eq_ite, Quotient.lift_mk, ite_eq_left_iff, one_ne_zero, imp_false,
      Decidable.not_not]
    exact IsBrauerEquivalent.refl _
  map_add' A B := by
    induction A using Quotient.inductionOn' with | h A
    induction B using Quotient.inductionOn' with | h B
    have hab' : @HAdd.hAdd (Additive (BrauerGroup ℝ)) _
      _ instHAdd (Quotient.mk'' A) (Quotient.mk'' B)=
      (Quotient.mk'' (mul A B) : Additive _) := rfl
    rw [hab']
    simp only [dite_eq_ite, Quotient.lift_mk]
    if hA : IsBrauerEquivalent A one_in' then
      if hB : IsBrauerEquivalent B one_in' then
        simp only [hA, ↓reduceIte, hB, add_zero, ite_eq_left_iff, one_ne_zero, imp_false,
          Decidable.not_not]
        have := eqv_tensor_eqv _ _ _ _ hA hB
        refine this.trans ?_
        change IsBrauerEquivalent ⟨.of ℝ (ℝ ⊗[ℝ] ℝ)⟩ ⟨.of ℝ ℝ⟩
        exact IsBrauerEquivalent.iso_to_eqv _ _ (BrauerGroupHom.someEquivs.e7.symm)
      else
      simp only [hA, ↓reduceIte, hB, zero_add, ite_eq_right_iff, zero_ne_one, imp_false]
      have : IsBrauerEquivalent (mul A B) B := by
        exact (eqv_tensor_eqv A one_in' B B hA (IsBrauerEquivalent.refl B)).trans <|
          IsBrauerEquivalent.iso_to_eqv _ _ (Algebra.TensorProduct.lid ℝ B)
      -- rw [this]
      by_contra! hBB
      haveI := this.symm.trans hBB
      tauto
    else
    if hB : IsBrauerEquivalent B one_in' then
    simp only [hA, ↓reduceIte, hB, add_zero, ite_eq_right_iff, zero_ne_one, imp_false]
    have : IsBrauerEquivalent (mul A B) A := by
      exact (eqv_tensor_eqv A A B one_in' (IsBrauerEquivalent.refl A) hB).trans <|
        IsBrauerEquivalent.iso_to_eqv _ _ (Algebra.TensorProduct.rid ℝ ℝ A)
    by_contra! hAA
    haveI := this.symm.trans hAA
    tauto
    else
    simp only [hA, ↓reduceIte, hB]
    change _ = 0
    change ¬ IsBrauerEquivalent _ ⟨.of ℝ ℝ⟩ at hA hB
    have hA1 := BrauerOverR A
    have hB1 := BrauerOverR B
    simp only [hA, false_or] at hA1
    simp only [hB, false_or] at hB1
    have : IsBrauerEquivalent (mul A B) one_in' :=
      (eqv_tensor_eqv A ⟨.of ℝ ℍ[ℝ]⟩ B ⟨.of ℝ ℍ[ℝ]⟩ hA1 hB1).trans <| by
        simpa [mul, one_in'] using QuaternionTensorEquivOne
    simp [this]

set_option linter.flexible false in
abbrev C2toBrauerOverR : ZMod 2 →+ Additive (BrauerGroup ℝ) where
  toFun x := if hx : x = 0 then Quotient.mk'' one_in' else Quotient.mk'' ⟨.of ℝ ℍ[ℝ]⟩
  map_zero' := by simp only [↓reduceDIte]; rfl
  map_add' x y := by
    let H : CSA ℝ := ⟨.of ℝ ℍ[ℝ]⟩
    fin_cases x <;> fin_cases y <;> simp only [dite_eq_ite]
    · change (1 : BrauerGroup ℝ) = 1 * 1
      simp
    · change ((Quotient.mk'' H : BrauerGroup ℝ)) = 1 * Quotient.mk'' H
      simp
    · change ((Quotient.mk'' H : BrauerGroup ℝ)) = Quotient.mk'' H * 1
      simp
    · change (1 : BrauerGroup ℝ) = Quotient.mk'' H * Quotient.mk'' H
      apply Quotient.sound
      change IsBrauerEquivalent one_in' (mul H H)
      exact QuaternionTensorEquivOne.symm

lemma toC2.left_inv : Function.LeftInverse C2toBrauerOverR toC2 := fun A ↦ by
  induction A using Quotient.inductionOn' with | h A
  obtain h1 | h2 := BrauerOverR A
  · change IsBrauerEquivalent A one_in' at h1
    simp only [AddMonoidHom.coe_mk, dite_eq_ite, ZeroHom.coe_mk, Quotient.lift_mk, h1, ↓reduceIte]
    rw [Quotient.sound']; exact h1.symm
  · have : ¬ (IsBrauerEquivalent A one_in') := fun h ↦ QuaternionNotEquivR <| h2.symm.trans h
    simp [this]
    exact Quotient.sound' h2.symm

lemma toC2.right_inv : Function.RightInverse C2toBrauerOverR toC2 := fun x ↦ by
  classical
  let H : CSA ℝ := ⟨.of ℝ ℍ[ℝ]⟩
  fin_cases x
  · change toC2 (if ((0 : ZMod 2) = 0) then Quotient.mk'' one_in' else Quotient.mk'' H) = 0
    rw [if_pos rfl]
    simp [toC2, IsBrauerEquivalent.refl]
  · change toC2 (if ((1 : ZMod 2) = 0) then Quotient.mk'' one_in' else Quotient.mk'' H) = 1
    have hone : ¬ ((1 : ZMod 2) = 0) := by norm_num
    rw [if_neg hone]
    change toC2 (Quotient.mk'' H) = (1 : ZMod 2)
    change (if IsBrauerEquivalent H one_in' then (0 : ZMod 2) else 1) = 1
    have hH : ¬ IsBrauerEquivalent H one_in' := by
      exact QuaternionNotEquivR
    rw [if_neg hH]

def BrauerGroupOverR : Additive (BrauerGroup ℝ) ≃+ ZMod 2 where
  toFun := toC2
  invFun := C2toBrauerOverR
  left_inv := toC2.left_inv
  right_inv := toC2.right_inv
  map_add' := toC2.map_add
