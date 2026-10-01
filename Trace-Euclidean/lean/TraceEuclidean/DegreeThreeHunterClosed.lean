import TraceEuclidean.CubicGeneratorSpread

/-!
# Closed Hunter certificate for totally real cubic fields

This module assembles the geometric short-vector theorem, the primitive
algebraic-integer lift, the coefficient-spread identity, and the integral
index formula.  It discharges `DegreeThreeHunterCertificateInput` and
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
theorem degree_three_hunterCertificate :
    DegreeThreeHunterCertificateInput := by
  intro K hreal hdegree hdisc
  have hdisc' : |NumberField.discr K.1| < 49 := by
    simpa only [NumberFieldCode.discriminant] using hdisc
  obtain ⟨bz, hbzero, x, hx, hgen, hshort⟩ :=
    cubic_hunter_generator K.1 hreal hdegree hdisc'
  let a : 𝓞 K.1 := hunterAlgebraicIntegerLift K.1 bz x
  change IntermediateField.adjoin ℚ {(a : K.1)} = ⊤ at hgen
  obtain ⟨bO, hbO⟩ := exists_ringOfIntegers_basis_one K.1 hdegree
  obtain ⟨index, hindex, hrelation⟩ :=
    cubic_exists_positive_index K.1 hdegree a hgen bO
  refine ⟨cubicS1 K.1 a, cubicS2 K.1 a,
    cubicS3 K.1 a, index, ?_, ?_, hindex, ?_⟩
  · have hbzero' : (bz.ofZLatticeBasis ℝ) 0 =
        euclideanOne K.1 := by
      rw [show (bz.ofZLatticeBasis ℝ) 0 =
          (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
            NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) by
        exact bz.ofZLatticeBasis_apply ℝ
          (NumberField.mixedEmbedding.euclidean.integerLattice K.1) 0]
      exact hbzero
    have he : inner ℝ (euclideanOne K.1)
        (euclideanOne K.1) ≠ 0 := by
      rw [inner_euclideanOne_self_eq_three K.1 hreal hdegree]
      norm_num
    have hshort' :
        3 * ‖hunterCenterLinearMap (euclideanOne K.1) he
          (euclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 16 := by
      change 3 * ‖hunterCenter (euclideanOne K.1)
        (euclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 16
      change 3 * ‖hunterCenter ((bz.ofZLatticeBasis ℝ) 0)
        ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
          (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 16 at hshort
      rw [hbzero'] at hshort
      unfold euclideanEmbedding at ⊢
      exact hshort
    have hspread := cubicSpread_cast_eq_center_norm
      K.1 hreal hdegree a hgen he
    have hspreadReal :
        ((cubicSpread (cubicS1 K.1 a)
          (cubicS2 K.1 a) : ℤ) : ℝ) < 16 := by
      rw [hspread]
      exact hshort'
    exact_mod_cast hspreadReal
  · exact cubic_minpoly_no_integer_root K.1 hdegree a hgen
  · simpa only [NumberFieldCode.discriminant] using hrelation

/-- The totally real cubic discriminant bound, with the Hunter certificate
fully discharged rather than supplied as an assumption. -/
theorem coded_degree_three_discriminant_ge_49
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 3) :
    (49 : ℝ) ≤ ((|K.discriminant| : ℤ) : ℝ) :=
  coded_degree_three_discriminant_ge_49_of_hunterCertificate
    degree_three_hunterCertificate K hreal hdegree

end

end TraceEuclidean
