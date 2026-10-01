import TraceEuclidean.QuarticGeneratorArithmetic

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

theorem quarticPolynomial_shift (s1 s2 s3 s4 k : ℤ) :
    quarticPolynomial
        (quarticShiftS1 s1 k)
        (quarticShiftS2 s1 s2 k)
        (quarticShiftS3 s1 s2 s3 k)
        (quarticShiftS4 s1 s2 s3 s4 k) =
      (quarticPolynomial s1 s2 s3 s4).comp (X + C k) := by
  simp [quarticPolynomial, quarticShiftS1,
    quarticShiftS2, quarticShiftS3, quarticShiftS4]
  ring

theorem quartic_minpoly_sub_integer
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

theorem quartic_generator_sub_integer_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (k : ℤ) :
    let b : 𝓞 K := a - algebraMap ℤ (𝓞 K) k
    IntermediateField.adjoin ℚ {(b : K)} = ⊤ ∧
      quarticS1 K b = quarticShiftS1 (quarticS1 K a) k ∧
      quarticS2 K b = quarticShiftS2
        (quarticS1 K a) (quarticS2 K a) k ∧
      quarticS3 K b = quarticShiftS3
        (quarticS1 K a) (quarticS2 K a)
        (quarticS3 K a) k ∧
      quarticS4 K b = quarticShiftS4
        (quarticS1 K a) (quarticS2 K a)
        (quarticS3 K a) (quarticS4 K a) k := by
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
      quarticPolynomial
          (quarticShiftS1 (quarticS1 K a) k)
          (quarticShiftS2 (quarticS1 K a)
            (quarticS2 K a) k)
          (quarticShiftS3 (quarticS1 K a)
            (quarticS2 K a) (quarticS3 K a) k)
          (quarticShiftS4 (quarticS1 K a)
            (quarticS2 K a) (quarticS3 K a)
            (quarticS4 K a) k) = minpoly ℤ (b : K) := by
    rw [quarticPolynomial_shift]
    rw [quarticPolynomial_eq_minpoly K hdegree a hgen]
    rw [hbcoe, quartic_minpoly_sub_integer]
  have hpB := quarticPolynomial_eq_minpoly K hdegree b hgenb
  have heq := hpB.trans hpShift.symm
  have hzero := congrArg (fun p : Polynomial ℤ ↦ p.eval 0) heq
  have hone := congrArg (fun p : Polynomial ℤ ↦ p.eval 1) heq
  have hnegOne := congrArg (fun p : Polynomial ℤ ↦ p.eval (-1)) heq
  have htwo := congrArg (fun p : Polynomial ℤ ↦ p.eval 2) heq
  norm_num [quarticPolynomial] at hzero hone hnegOne htwo
  refine ⟨hgenb, ?_, ?_, ?_, ?_⟩
  all_goals linarith

theorem quarticPolynomial_neg (s1 s2 s3 s4 : ℤ) :
    quarticPolynomial (-s1) s2 (-s3) s4 =
      (quarticPolynomial s1 s2 s3 s4).comp (-X) := by
  simp [quarticPolynomial]
  ring

theorem quartic_minpoly_neg
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

theorem quartic_generator_neg_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    IntermediateField.adjoin ℚ {((-a : 𝓞 K) : K)} = ⊤ ∧
      quarticS1 K (-a) = -quarticS1 K a ∧
      quarticS2 K (-a) = quarticS2 K a ∧
      quarticS3 K (-a) = -quarticS3 K a ∧
      quarticS4 K (-a) = quarticS4 K a := by
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
  have hpNeg : quarticPolynomial
      (-quarticS1 K a) (quarticS2 K a)
      (-quarticS3 K a) (quarticS4 K a) =
        minpoly ℤ ((-a : 𝓞 K) : K) := by
    rw [quarticPolynomial_neg]
    rw [quarticPolynomial_eq_minpoly K hdegree a hgen]
    simpa using (quartic_minpoly_neg K hdegree a hgen).symm
  have hpB := quarticPolynomial_eq_minpoly K hdegree (-a) hgenneg
  have heq := hpB.trans hpNeg.symm
  have hzero := congrArg (fun p : Polynomial ℤ ↦ p.eval 0) heq
  have hone := congrArg (fun p : Polynomial ℤ ↦ p.eval 1) heq
  have hnegOne := congrArg (fun p : Polynomial ℤ ↦ p.eval (-1)) heq
  have htwo := congrArg (fun p : Polynomial ℤ ↦ p.eval 2) heq
  norm_num [quarticPolynomial] at hzero hone hnegOne htwo
  refine ⟨hgenneg, ?_, ?_, ?_, ?_⟩
  all_goals linarith

theorem exists_normalized_quartic_generator
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∃ b : 𝓞 K,
      IntermediateField.adjoin ℚ {(b : K)} = ⊤ ∧
      (quarticS1 K b = 0 ∨ quarticS1 K b = 1 ∨
        quarticS1 K b = 2) ∧
      quarticSpread (quarticS1 K b) (quarticS2 K b) =
        quarticSpread (quarticS1 K a) (quarticS2 K a) ∧
      quarticHermiteMinorThree (quarticS1 K b)
          (quarticS2 K b) (quarticS3 K b)
          (quarticS4 K b) =
        quarticHermiteMinorThree (quarticS1 K a)
          (quarticS2 K a) (quarticS3 K a)
          (quarticS4 K a) ∧
      quarticDiscriminant (quarticS1 K b)
          (quarticS2 K b) (quarticS3 K b)
          (quarticS4 K b) =
        quarticDiscriminant (quarticS1 K a)
          (quarticS2 K a) (quarticS3 K a)
          (quarticS4 K a) := by
  let s1 := quarticS1 K a
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
        rcases quartic_generator_sub_integer_coefficients
            K hdegree a hgen k with
          ⟨hgenb, hs1, hs2, hs3, hs4⟩
        refine ⟨b, hgenb, ?_, ?_, ?_, ?_⟩
        · rw [hs1]
          simp only [quarticShiftS1, k, s1]
          omega
        · rw [hs1, hs2, quartic_shift_spread]
        · rw [hs1, hs2, hs3, hs4,
            quartic_shift_hermiteMinorThree]
        · rw [hs1, hs2, hs3, hs4,
            quartic_shift_discriminant]
    | · rcases quartic_generator_neg_coefficients
            K hdegree a hgen with
          ⟨hgenc, hc1, hc2, hc3, hc4⟩
        let c : 𝓞 K := -a
        let k : ℤ := -(s1 / 4) - 1
        let b : 𝓞 K := c - algebraMap ℤ (𝓞 K) k
        rcases quartic_generator_sub_integer_coefficients
            K hdegree c hgenc k with
          ⟨hgenb, hs1, hs2, hs3, hs4⟩
        refine ⟨b, hgenb, ?_, ?_, ?_, ?_⟩
        · rw [hs1, hc1]
          right
          left
          simp only [quarticShiftS1, k, s1]
          omega
        · rw [hs1, hs2, hc1, hc2,
            quartic_shift_spread, quartic_neg_spread]
        · rw [hs1, hs2, hs3, hs4, hc1, hc2, hc3, hc4,
            quartic_shift_hermiteMinorThree,
            quartic_neg_hermiteMinorThree]
        · rw [hs1, hs2, hs3, hs4, hc1, hc2, hc3, hc4,
            quartic_shift_discriminant,
            quartic_neg_discriminant]

end
end TraceEuclidean
