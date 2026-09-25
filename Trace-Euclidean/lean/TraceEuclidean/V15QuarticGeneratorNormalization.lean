import TraceEuclidean.V15QuarticGeneratorArithmetic

/-!
# Normalizing an actual primitive quartic generator

The coefficient normalization used by the finite quartic search is lifted
here to algebraic integers.  Integer translation and root negation preserve
field generation, and the four signed coefficients of the resulting minimal
polynomial agree with the explicit coefficient transformations.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped NumberField

theorem v15_quarticPolynomial_shift (s1 s2 s3 s4 k : ℤ) :
    v15QuarticPolynomial
        (v15QuarticShiftS1 s1 k)
        (v15QuarticShiftS2 s1 s2 k)
        (v15QuarticShiftS3 s1 s2 s3 k)
        (v15QuarticShiftS4 s1 s2 s3 s4 k) =
      (v15QuarticPolynomial s1 s2 s3 s4).comp (X + C k) := by
  simp [v15QuarticPolynomial, v15QuarticShiftS1,
    v15QuarticShiftS2, v15QuarticShiftS3, v15QuarticShiftS4]
  ring

theorem v15_quartic_minpoly_sub_integer
    (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (k : ℤ) :
    minpoly ℤ ((a : K) - algebraMap ℤ K k) =
      (minpoly ℤ (a : K)).comp (X + C k) := by
  have hbInt : IsIntegral ℤ ((a : K) - algebraMap ℤ K k) :=
    a.isIntegral_coe.sub (isIntegral_algebraMap)
  apply Polynomial.map_injective (algebraMap ℤ ℚ)
    (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hbInt,
    map_comp]
  have h := minpoly.sub_algebraMap (A := ℚ) (a : K) (k : ℚ)
  have hminAQ : minpoly ℚ (a : K) =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hminAQ] at h
  simpa using h

theorem v15_quartic_generator_sub_integer_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (k : ℤ) :
    let b : 𝓞 K := a - algebraMap ℤ (𝓞 K) k
    IntermediateField.adjoin ℚ {(b : K)} = ⊤ ∧
      v15QuarticS1 K b = v15QuarticShiftS1 (v15QuarticS1 K a) k ∧
      v15QuarticS2 K b = v15QuarticShiftS2
        (v15QuarticS1 K a) (v15QuarticS2 K a) k ∧
      v15QuarticS3 K b = v15QuarticShiftS3
        (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) k ∧
      v15QuarticS4 K b = v15QuarticShiftS4
        (v15QuarticS1 K a) (v15QuarticS2 K a)
        (v15QuarticS3 K a) (v15QuarticS4 K a) k := by
  dsimp only
  let b : 𝓞 K := a - algebraMap ℤ (𝓞 K) k
  have hbcoe : (b : K) = (a : K) - algebraMap ℤ K k := by
    simp [b]
  have hbcoeQ : (b : K) = (a : K) - algebraMap ℚ K (k : ℚ) := by
    simp [b]
  have hadeg : (minpoly ℚ (a : K)).natDegree = 4 := by
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have hbdeg : (minpoly ℚ (b : K)).natDegree = 4 := by
    rw [hbcoeQ, minpoly.sub_algebraMap, natDegree_comp,
      natDegree_X_add_C, mul_one]
    exact hadeg
  have hgenb : IntermediateField.adjoin ℚ {(b : K)} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq]
    exact hbdeg.trans hdegree.symm
  have hpShift :
      v15QuarticPolynomial
          (v15QuarticShiftS1 (v15QuarticS1 K a) k)
          (v15QuarticShiftS2 (v15QuarticS1 K a)
            (v15QuarticS2 K a) k)
          (v15QuarticShiftS3 (v15QuarticS1 K a)
            (v15QuarticS2 K a) (v15QuarticS3 K a) k)
          (v15QuarticShiftS4 (v15QuarticS1 K a)
            (v15QuarticS2 K a) (v15QuarticS3 K a)
            (v15QuarticS4 K a) k) = minpoly ℤ (b : K) := by
    rw [v15_quarticPolynomial_shift]
    rw [v15_quarticPolynomial_eq_minpoly K hdegree a hgen]
    rw [hbcoe, v15_quartic_minpoly_sub_integer]
  have hpB := v15_quarticPolynomial_eq_minpoly K hdegree b hgenb
  have heq := hpB.trans hpShift.symm
  have hzero := congrArg (fun p : Polynomial ℤ ↦ p.eval 0) heq
  have hone := congrArg (fun p : Polynomial ℤ ↦ p.eval 1) heq
  have hnegOne := congrArg (fun p : Polynomial ℤ ↦ p.eval (-1)) heq
  have htwo := congrArg (fun p : Polynomial ℤ ↦ p.eval 2) heq
  norm_num [v15QuarticPolynomial] at hzero hone hnegOne htwo
  refine ⟨hgenb, ?_, ?_, ?_, ?_⟩
  all_goals linarith

theorem v15_quarticPolynomial_neg (s1 s2 s3 s4 : ℤ) :
    v15QuarticPolynomial (-s1) s2 (-s3) s4 =
      (v15QuarticPolynomial s1 s2 s3 s4).comp (-X) := by
  simp [v15QuarticPolynomial]
  ring

theorem v15_quartic_minpoly_neg
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    minpoly ℤ (-(a : K)) = (minpoly ℤ (a : K)).comp (-X) := by
  have hnegInt : IsIntegral ℤ (-(a : K)) := a.isIntegral_coe.neg
  have hadeg : (minpoly ℚ (a : K)).natDegree = 4 := by
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  apply Polynomial.map_injective (algebraMap ℤ ℚ)
    (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hnegInt,
    map_comp]
  have h := minpoly.neg (A := ℚ) (a : K)
  have hminAQ : minpoly ℚ (a : K) =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hadeg] at h
  norm_num at h
  rw [hminAQ] at h
  simpa using h

theorem v15_quartic_generator_neg_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    IntermediateField.adjoin ℚ {((-a : 𝓞 K) : K)} = ⊤ ∧
      v15QuarticS1 K (-a) = -v15QuarticS1 K a ∧
      v15QuarticS2 K (-a) = v15QuarticS2 K a ∧
      v15QuarticS3 K (-a) = -v15QuarticS3 K a ∧
      v15QuarticS4 K (-a) = v15QuarticS4 K a := by
  have hadeg : (minpoly ℚ (a : K)).natDegree = 4 := by
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have hnegdeg : (minpoly ℚ (-((a : 𝓞 K) : K))).natDegree = 4 := by
    rw [minpoly.neg, hadeg]
    norm_num
    rw [natDegree_comp]
    norm_num
    exact hadeg
  have hgenneg : IntermediateField.adjoin ℚ {((-a : 𝓞 K) : K)} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq]
    exact hnegdeg.trans hdegree.symm
  have hpNeg : v15QuarticPolynomial
      (-v15QuarticS1 K a) (v15QuarticS2 K a)
      (-v15QuarticS3 K a) (v15QuarticS4 K a) =
        minpoly ℤ ((-a : 𝓞 K) : K) := by
    rw [v15_quarticPolynomial_neg]
    rw [v15_quarticPolynomial_eq_minpoly K hdegree a hgen]
    simpa using (v15_quartic_minpoly_neg K hdegree a hgen).symm
  have hpB := v15_quarticPolynomial_eq_minpoly K hdegree (-a) hgenneg
  have heq := hpB.trans hpNeg.symm
  have hzero := congrArg (fun p : Polynomial ℤ ↦ p.eval 0) heq
  have hone := congrArg (fun p : Polynomial ℤ ↦ p.eval 1) heq
  have hnegOne := congrArg (fun p : Polynomial ℤ ↦ p.eval (-1)) heq
  have htwo := congrArg (fun p : Polynomial ℤ ↦ p.eval 2) heq
  norm_num [v15QuarticPolynomial] at hzero hone hnegOne htwo
  refine ⟨hgenneg, ?_, ?_, ?_, ?_⟩
  all_goals linarith

theorem v15_exists_normalized_quartic_generator
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∃ b : 𝓞 K,
      IntermediateField.adjoin ℚ {(b : K)} = ⊤ ∧
      (v15QuarticS1 K b = 0 ∨ v15QuarticS1 K b = 1 ∨
        v15QuarticS1 K b = 2) ∧
      v15QuarticSpread (v15QuarticS1 K b) (v15QuarticS2 K b) =
        v15QuarticSpread (v15QuarticS1 K a) (v15QuarticS2 K a) ∧
      v15QuarticHermiteMinorThree (v15QuarticS1 K b)
          (v15QuarticS2 K b) (v15QuarticS3 K b)
          (v15QuarticS4 K b) =
        v15QuarticHermiteMinorThree (v15QuarticS1 K a)
          (v15QuarticS2 K a) (v15QuarticS3 K a)
          (v15QuarticS4 K a) ∧
      v15QuarticDiscriminant (v15QuarticS1 K b)
          (v15QuarticS2 K b) (v15QuarticS3 K b)
          (v15QuarticS4 K b) =
        v15QuarticDiscriminant (v15QuarticS1 K a)
          (v15QuarticS2 K a) (v15QuarticS3 K a)
          (v15QuarticS4 K a) := by
  let s1 := v15QuarticS1 K a
  have hremNonneg : 0 ≤ s1 % 4 :=
    Int.emod_nonneg s1 (by norm_num)
  have hremLt : s1 % 4 < 4 :=
    Int.emod_lt_of_pos s1 (by norm_num)
  have hdecomp : s1 / 4 * 4 + s1 % 4 = s1 :=
    Int.ediv_mul_add_emod s1 4
  interval_cases hrem : s1 % 4
  all_goals first
    | · let k : ℤ := s1 / 4
        let b : 𝓞 K := a - algebraMap ℤ (𝓞 K) k
        rcases v15_quartic_generator_sub_integer_coefficients
            K hdegree a hgen k with
          ⟨hgenb, hs1, hs2, hs3, hs4⟩
        refine ⟨b, hgenb, ?_, ?_, ?_, ?_⟩
        · rw [hs1]
          simp only [v15QuarticShiftS1, k, s1]
          omega
        · rw [hs1, hs2, v15_quartic_shift_spread]
        · rw [hs1, hs2, hs3, hs4,
            v15_quartic_shift_hermiteMinorThree]
        · rw [hs1, hs2, hs3, hs4,
            v15_quartic_shift_discriminant]
    | · rcases v15_quartic_generator_neg_coefficients
            K hdegree a hgen with
          ⟨hgenc, hc1, hc2, hc3, hc4⟩
        let c : 𝓞 K := -a
        let k : ℤ := -(s1 / 4) - 1
        let b : 𝓞 K := c - algebraMap ℤ (𝓞 K) k
        rcases v15_quartic_generator_sub_integer_coefficients
            K hdegree c hgenc k with
          ⟨hgenb, hs1, hs2, hs3, hs4⟩
        refine ⟨b, hgenb, ?_, ?_, ?_, ?_⟩
        · rw [hs1, hc1]
          right
          left
          simp only [v15QuarticShiftS1, k, s1]
          omega
        · rw [hs1, hs2, hc1, hc2,
            v15_quartic_shift_spread, v15_quartic_neg_spread]
        · rw [hs1, hs2, hs3, hs4, hc1, hc2, hc3, hc4,
            v15_quartic_shift_hermiteMinorThree,
            v15_quartic_neg_hermiteMinorThree]
        · rw [hs1, hs2, hs3, hs4, hc1, hc2, hc3, hc4,
            v15_quartic_shift_discriminant,
            v15_quartic_neg_discriminant]

end
end TraceEuclidean
