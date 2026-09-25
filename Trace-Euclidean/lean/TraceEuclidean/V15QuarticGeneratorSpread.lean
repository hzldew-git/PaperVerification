import TraceEuclidean.V15QuarticGeneratorArithmetic
import TraceEuclidean.V15CubicGeneratorSpread

/-!
# Trace and Euclidean-spread bridge for quartic generators

This module identifies the quartic coefficient expression used by the finite
enumeration with four times the squared norm of the centered Minkowski
embedding of a primitive quartic algebraic integer.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial Finset
open scoped NumberField

open scoped Classical in
/-- In a totally real quartic field, the diagonal vector has squared
Euclidean norm four. -/
theorem v15_inner_euclideanOne_self_eq_four
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) :
    inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) = 4 := by
  letI : NumberField.IsTotallyReal K := hreal
  unfold v15EuclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← NumberField.IsTotallyReal.finrank K, hdegree]

/-- The trace of a primitive quartic generator is its first signed integral
coefficient. -/
theorem v15_quartic_trace_eq_s1
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K (a : K) = (v15QuarticS1 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, v15QuarticS1, Polynomial.coeff_map] using ht

/-- Newton's second identity for a primitive quartic generator. -/
theorem v15_quartic_trace_sq_eq_s1_sq_sub_two_s2
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 2) =
      (v15QuarticS1 K a : ℚ) ^ 2 -
        2 * (v15QuarticS2 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_sq_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, v15QuarticS1, v15QuarticS2,
    Polynomial.coeff_map] using ht

/-- Newton's third identity for a primitive quartic generator. -/
theorem v15_quartic_trace_cube_eq_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 3) =
      (v15QuarticS1 K a : ℚ) ^ 3 -
        3 * (v15QuarticS1 K a : ℚ) * (v15QuarticS2 K a : ℚ) +
        3 * (v15QuarticS3 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_cube_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  have ht' : Algebra.trace ℚ K ((a : K) ^ 3) =
      -((minpoly ℤ (a : K)).coeff 3 : ℚ) ^ 3 +
        3 * ((minpoly ℤ (a : K)).coeff 3 : ℚ) *
          ((minpoly ℤ (a : K)).coeff 2 : ℚ) -
        3 * ((minpoly ℤ (a : K)).coeff 1 : ℚ) := by
    simpa [pb, Polynomial.coeff_map] using ht
  rw [ht']
  simp only [v15QuarticS1, v15QuarticS2, v15QuarticS3]
  push_cast
  ring

/-- Newton's fourth identity for a primitive quartic generator. -/
theorem v15_quartic_trace_fourth_eq_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 4) =
      (v15QuarticS1 K a : ℚ) ^ 4 -
        4 * (v15QuarticS1 K a : ℚ) ^ 2 * (v15QuarticS2 K a : ℚ) +
        2 * (v15QuarticS2 K a : ℚ) ^ 2 +
        4 * (v15QuarticS1 K a : ℚ) * (v15QuarticS3 K a : ℚ) -
        4 * (v15QuarticS4 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_fourth_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  have ht' : Algebra.trace ℚ K ((a : K) ^ 4) =
      ((minpoly ℤ (a : K)).coeff 3 : ℚ) ^ 4 -
        4 * ((minpoly ℤ (a : K)).coeff 3 : ℚ) ^ 2 *
          ((minpoly ℤ (a : K)).coeff 2 : ℚ) +
        2 * ((minpoly ℤ (a : K)).coeff 2 : ℚ) ^ 2 +
        4 * ((minpoly ℤ (a : K)).coeff 3 : ℚ) *
          ((minpoly ℤ (a : K)).coeff 1 : ℚ) -
        4 * ((minpoly ℤ (a : K)).coeff 0 : ℚ) := by
    simpa [pb, Polynomial.coeff_map] using ht
  rw [ht']
  simp only [v15QuarticS1, v15QuarticS2, v15QuarticS3,
    v15QuarticS4]
  push_cast
  ring

open scoped Classical in
/-- The centered Euclidean norm is the standard quartic trace expression. -/
theorem v15_quartic_center_norm_eq_trace_expression
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) (a : K) :
    let e := v15EuclideanOne K
    let he : inner ℝ e e ≠ 0 := by
      rw [v15_inner_euclideanOne_self_eq_four K hreal hdegree]
      norm_num
    4 * ‖v15HunterCenterLinearMap e he (v15EuclideanEmbedding K a)‖ ^ 2 =
      4 * ((Algebra.trace ℚ K (a ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K a : ℚ) : ℝ) ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  dsimp only
  let he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0 := by
    rw [v15_inner_euclideanOne_self_eq_four K hreal hdegree]
    norm_num
  rw [← real_inner_self_eq_norm_sq]
  change 4 * inner ℝ
      (v15HunterCenter (v15EuclideanOne K) (v15EuclideanEmbedding K a))
      (v15HunterCenter (v15EuclideanOne K) (v15EuclideanEmbedding K a)) = _
  rw [v15_inner_center_center (v15EuclideanOne K)
    (v15EuclideanEmbedding K a) (v15EuclideanEmbedding K a) he]
  rw [v15_inner_euclideanOne_self_eq_four K hreal hdegree]
  rw [v15_inner_euclideanOne_euclideanEmbedding K a]
  rw [v15_inner_euclideanEmbedding_self K a]
  ring

open scoped Classical in
/-- Exact bridge from the quartic coefficient spread to the Hunter centered
norm. -/
theorem v15_quarticSpread_cast_eq_center_norm
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (he : inner ℝ (v15EuclideanOne K) (v15EuclideanOne K) ≠ 0) :
    ((v15QuarticSpread (v15QuarticS1 K a)
        (v15QuarticS2 K a) : ℤ) : ℝ) =
      4 * ‖v15HunterCenterLinearMap (v15EuclideanOne K) he
        (v15EuclideanEmbedding K (a : K))‖ ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  rw [v15_quartic_center_norm_eq_trace_expression
    K hreal hdegree (a : K)]
  rw [v15_quartic_trace_eq_s1 K hdegree a hgen]
  rw [v15_quartic_trace_sq_eq_s1_sq_sub_two_s2
    K hdegree a hgen]
  push_cast
  simp only [v15QuarticSpread, v15QuarticSecondPowerSum]
  push_cast
  ring

end

end TraceEuclidean
