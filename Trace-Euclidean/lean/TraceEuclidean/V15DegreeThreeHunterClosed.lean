import TraceEuclidean.V15CubicGeneratorSpread

/-!
# Closed Hunter certificate for totally real cubic fields

This module assembles the geometric short-vector theorem, the primitive
algebraic-integer lift, the coefficient-spread identity, and the integral
index formula.  It discharges `V15DegreeThreeHunterCertificateInput` and
therefore removes the former abstract input from the cubic discriminant
bound.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Submodule
open scoped NumberField

set_option maxHeartbeats 1000000 in
-- Simplifying the dependent orthogonal-complement type after replacing the
-- first lattice basis vector by the diagonal vector exceeds the default.
open scoped Classical in
/-- The complete Hunter certificate is constructed internally from the
geometry of the Euclidean Minkowski lattice. -/
theorem v15_degree_three_hunterCertificate :
    V15DegreeThreeHunterCertificateInput := by
  intro K hreal hdegree hdisc
  have hdisc' : |NumberField.discr K.1| < 49 := by
    simpa only [NumberFieldCode.discriminant] using hdisc
  obtain ⟨bz, hbzero, x, hx, hgen, hshort⟩ :=
    v15_cubic_hunter_generator K.1 hreal hdegree hdisc'
  let a : 𝓞 K.1 := v15HunterAlgebraicIntegerLift K.1 bz x
  change IntermediateField.adjoin ℚ {(a : K.1)} = ⊤ at hgen
  obtain ⟨bO, hbO⟩ := v15_exists_ringOfIntegers_basis_one K.1 hdegree
  obtain ⟨index, hindex, hrelation⟩ :=
    v15_cubic_exists_positive_index K.1 hdegree a hgen bO
  refine ⟨v15CubicS1 K.1 a, v15CubicS2 K.1 a,
    v15CubicS3 K.1 a, index, ?_, ?_, hindex, ?_⟩
  · have hbzero' : (bz.ofZLatticeBasis ℝ) 0 =
        v15EuclideanOne K.1 := by
      rw [show (bz.ofZLatticeBasis ℝ) 0 =
          (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) by
        exact bz.ofZLatticeBasis_apply ℝ
          (NumberField.mixedEmbedding.euclidean.integerLattice K.1) 0]
      exact hbzero
    have he : inner ℝ (v15EuclideanOne K.1)
        (v15EuclideanOne K.1) ≠ 0 := by
      rw [v15_inner_euclideanOne_self_eq_three K.1 hreal hdegree]
      norm_num
    have hshort' :
        3 * ‖v15HunterCenterLinearMap (v15EuclideanOne K.1) he
          (v15EuclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 16 := by
      change 3 * ‖v15HunterCenter (v15EuclideanOne K.1)
        (v15EuclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 16
      change 3 * ‖v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
        ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
          (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 16 at hshort
      rw [hbzero'] at hshort
      unfold v15EuclideanEmbedding at ⊢
      exact hshort
    have hspread := v15_cubicSpread_cast_eq_center_norm
      K.1 hreal hdegree a hgen he
    have hspreadReal :
        ((v15CubicSpread (v15CubicS1 K.1 a)
          (v15CubicS2 K.1 a) : ℤ) : ℝ) < 16 := by
      rw [hspread]
      exact hshort'
    exact_mod_cast hspreadReal
  · exact v15_cubic_minpoly_no_integer_root K.1 hdegree a hgen
  · simpa only [NumberFieldCode.discriminant] using hrelation

/-- The totally real cubic discriminant bound, with the Hunter certificate
fully discharged rather than supplied as an assumption. -/
theorem v15_coded_degree_three_discriminant_ge_49
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 3) :
    (49 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) :=
  v15_coded_degree_three_discriminant_ge_49_of_hunterCertificate
    v15_degree_three_hunterCertificate K hreal hdegree

end

end TraceEuclidean
