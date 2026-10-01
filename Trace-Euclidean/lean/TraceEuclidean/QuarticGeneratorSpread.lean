import TraceEuclidean.QuarticGeneratorArithmetic
import TraceEuclidean.CubicGeneratorSpread

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
theorem inner_euclideanOne_self_eq_four
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) :
    inner ℝ (euclideanOne K) (euclideanOne K) = 4 := by
  letI : NumberField.IsTotallyReal K := hreal
  unfold euclideanOne
  rw [WithLp.prod_inner_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [← NumberField.IsTotallyReal.finrank K, hdegree]

/-- The trace of a primitive quartic generator is its first signed integral
coefficient. -/
theorem quartic_trace_eq_s1
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K (a : K) = (quarticS1 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := powerBasis_trace_gen_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, quarticS1, Polynomial.coeff_map] using ht

/-- Newton's second identity for a primitive quartic generator. -/
theorem quartic_trace_sq_eq_s1_sq_sub_two_s2
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 2) =
      (quarticS1 K a : ℚ) ^ 2 -
        2 * (quarticS2 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := powerBasis_trace_gen_sq_dim_four pb hdim
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, quarticS1, quarticS2,
    Polynomial.coeff_map] using ht

/-- Newton's third identity for a primitive quartic generator. -/
theorem quartic_trace_cube_eq_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 3) =
      (quarticS1 K a : ℚ) ^ 3 -
        3 * (quarticS1 K a : ℚ) * (quarticS2 K a : ℚ) +
        3 * (quarticS3 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := powerBasis_trace_gen_cube_dim_four pb hdim
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
  simp only [quarticS1, quarticS2, quarticS3]
  push_cast
  ring

/-- Newton's fourth identity for a primitive quartic generator. -/
theorem quartic_trace_fourth_eq_coefficients
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 4) =
      (quarticS1 K a : ℚ) ^ 4 -
        4 * (quarticS1 K a : ℚ) ^ 2 * (quarticS2 K a : ℚ) +
        2 * (quarticS2 K a : ℚ) ^ 2 +
        4 * (quarticS1 K a : ℚ) * (quarticS3 K a : ℚ) -
        4 * (quarticS4 K a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := powerBasis_trace_gen_fourth_dim_four pb hdim
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
  simp only [quarticS1, quarticS2, quarticS3,
    quarticS4]
  push_cast
  ring

open scoped Classical in
/-- The centered Euclidean norm is the standard quartic trace expression. -/
theorem quartic_center_norm_eq_trace_expression
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) (a : K) :
    let e := euclideanOne K
    let he : inner ℝ e e ≠ 0 := by
      rw [inner_euclideanOne_self_eq_four K hreal hdegree]
      norm_num
    4 * ‖hunterCenterLinearMap e he (euclideanEmbedding K a)‖ ^ 2 =
      4 * ((Algebra.trace ℚ K (a ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K a : ℚ) : ℝ) ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  dsimp only
  let he : inner ℝ (euclideanOne K) (euclideanOne K) ≠ 0 := by
    rw [inner_euclideanOne_self_eq_four K hreal hdegree]
    norm_num
  rw [← real_inner_self_eq_norm_sq]
  change 4 * inner ℝ
      (hunterCenter (euclideanOne K) (euclideanEmbedding K a))
      (hunterCenter (euclideanOne K) (euclideanEmbedding K a)) = _
  rw [inner_center_center (euclideanOne K)
    (euclideanEmbedding K a) (euclideanEmbedding K a) he]
  rw [inner_euclideanOne_self_eq_four K hreal hdegree]
  rw [inner_euclideanOne_euclideanEmbedding K a]
  rw [inner_euclideanEmbedding_self K a]
  ring

open scoped Classical in
/-- Exact bridge from the quartic coefficient spread to the Hunter centered
norm. -/
theorem quarticSpread_cast_eq_center_norm
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (he : inner ℝ (euclideanOne K) (euclideanOne K) ≠ 0) :
    ((quarticSpread (quarticS1 K a)
        (quarticS2 K a) : ℤ) : ℝ) =
      4 * ‖hunterCenterLinearMap (euclideanOne K) he
        (euclideanEmbedding K (a : K))‖ ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  rw [quartic_center_norm_eq_trace_expression
    K hreal hdegree (a : K)]
  rw [quartic_trace_eq_s1 K hdegree a hgen]
  rw [quartic_trace_sq_eq_s1_sq_sub_two_s2
    K hdegree a hgen]
  push_cast
  simp only [quarticSpread, quarticSecondPowerSum]
  push_cast
  ring

end

end TraceEuclidean
