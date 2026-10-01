import TraceEuclidean.QuarticHermite
import TraceEuclidean.PrimitiveBasis
import TraceEuclidean.QuarticHunterNumberFieldProjection

/-!
# Reduction of the quartic Hunter certificate to a primitive short generator

The finite quartic enumeration no longer needs to assume irreducibility, an
index-discriminant identity, or positivity of the third Hermite minor. This
module derives those parts from an actual primitive algebraic integer. The
remaining input is confined to constructing a primitive quartic Hunter
generator with the strict upper-spread bound. Trace normalization and all
coefficient bounds are now derived internally.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped NumberField

open scoped Classical in
/-- The remaining composite-degree selection problem in the quartic Hunter
argument. It says that, under the small-discriminant hypothesis, a nonzero
short vector in the projected lattice can be chosen so that its integral
lift generates the whole quartic field. -/
def QuarticPrimitiveShortSelectionInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K.1)),
      ((((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) =
          euclideanOne K.1) →
      (∃ x : quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        4 * ‖((x : quarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 29) →
      ∃ x : quarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        IntermediateField.adjoin ℚ
          {((quarticHunterAlgebraicIntegerLift K.1 bz x : 𝓞 K.1) :
            K.1)} = ⊤ ∧
        4 * ‖((x : quarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 29

/-- The residual mathematical content of the quartic Hunter step. It asks
only for an actual primitive integral generator satisfying the strict
upper-spread bound. -/
def DegreeFourPrimitiveGeneratorInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 →
      |K.discriminant| < 725 →
      ∃ a : 𝓞 K.1,
        IntermediateField.adjoin ℚ {((a : 𝓞 K.1) : K.1)} = ⊤ ∧
        quarticSpread (quarticS1 K.1 a)
          (quarticS2 K.1 a) < 29

set_option maxHeartbeats 0 in
-- Rewriting the dependent orthogonal-complement type after identifying the
-- first basis vector with the diagonal vector needs additional reduction.
open scoped Classical in
/-- The sharp three-dimensional Hermite theorem and the explicit
composite-degree selection input imply the residual primitive-generator
statement. All lattice projection and coefficient-spread bridges are proved
internally. -/
theorem degree_four_primitiveGenerator_of_hermite_and_selection
    (hHermite : HermiteThreeInput.{0})
    (hSelection : QuarticPrimitiveShortSelectionInput) :
    DegreeFourPrimitiveGeneratorInput := by
  intro K hreal hdegree hdisc
  have hdisc' : |NumberField.discr K.1| < 725 := by
    simpa only [NumberFieldCode.discriminant] using hdisc
  obtain ⟨bz, hbzero, x, hx, hshort⟩ :=
    quartic_projected_shortVector
      hHermite K.1 hreal hdegree hdisc'
  obtain ⟨y, hy, hgen, hshort'⟩ :=
    hSelection K hreal hdegree hdisc bz hbzero ⟨x, hx, hshort⟩
  let a : 𝓞 K.1 := quarticHunterAlgebraicIntegerLift K.1 bz y
  change IntermediateField.adjoin ℚ {(a : K.1)} = ⊤ at hgen
  refine ⟨a, hgen, ?_⟩
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 =
      euclideanOne K.1 := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K.1) 0]
    exact hbzero
  have he : inner ℝ (euclideanOne K.1)
      (euclideanOne K.1) ≠ 0 := by
    rw [inner_euclideanOne_self_eq_four K.1 hreal hdegree]
    norm_num
  have hshortBasis :
      4 * ‖hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
          (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 29 := by
    change 4 * ‖hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
      ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
        (NumberField.mixedEmbedding K.1
          ((quarticHunterAlgebraicIntegerLift K.1 bz y : 𝓞 K.1) :
            K.1)))‖ ^ 2 < 29
    rw [quarticHunterAlgebraicIntegerLift_center K.1 bz y]
    exact hshort'
  have hshortCenter :
      4 * ‖hunterCenterLinearMap (euclideanOne K.1) he
        (euclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 29 := by
    change 4 * ‖hunterCenter (euclideanOne K.1)
      (euclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 29
    change 4 * ‖hunterCenter ((bz.ofZLatticeBasis ℝ) 0)
      ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
        (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 29 at hshortBasis
    rw [hbzero'] at hshortBasis
    unfold euclideanEmbedding at ⊢
    exact hshortBasis
  have hspread := quarticSpread_cast_eq_center_norm
    K.1 hreal hdegree a hgen he
  have hspreadReal :
      ((quarticSpread (quarticS1 K.1 a)
        (quarticS2 K.1 a) : ℤ) : ℝ) < 29 := by
    rw [hspread]
    exact hshortCenter
  exact_mod_cast hspreadReal

/-- An actual primitive generator with the residual Hunter bounds supplies
the complete normalized certificate required by the finite quartic
enumeration. Irreducibility, the positive polynomial discriminant, and the
positive index relation are derived internally. -/
theorem degree_four_hunterCertificate_of_primitiveGenerator
    (hGenerator : DegreeFourPrimitiveGeneratorInput) :
    DegreeFourHunterCertificateInput := by
  intro K hreal hdegree hdisc
  rcases hGenerator K hreal hdegree hdisc with
    ⟨a, hgen, hspreadLt⟩
  have hspreadPos :=
    quarticSpread_pos K.1 hreal hdegree a hgen
  have hminor :=
    quarticHermiteMinorThree_pos K.1 hreal hdegree a hgen
  obtain ⟨bO⟩ := exists_ringOfIntegers_basis_fin_four K.1 hdegree
  obtain ⟨index, hindex, hrelation⟩ :=
    quartic_exists_positive_index K.1 hdegree a hgen bO
  have hnoRoot :=
    quartic_minpoly_no_integer_root K.1 hdegree a hgen
  have hnoQuadratic :=
    quartic_minpoly_no_quadratic_factor K.1 hdegree a hgen
  letI : NumberField.IsTotallyReal K.1 := hreal
  have hsign : K.discriminant.sign = 1 := by
    rw [NumberFieldCode.discriminant, NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hfieldPos : 0 < K.discriminant :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hindexInt : (0 : ℤ) < index := by exact_mod_cast hindex
  have hsquare : (0 : ℤ) < (index : ℤ) ^ 2 := sq_pos_of_pos hindexInt
  have hrelation' :
      quarticDiscriminant (quarticS1 K.1 a)
          (quarticS2 K.1 a) (quarticS3 K.1 a)
          (quarticS4 K.1 a) =
        (index : ℤ) ^ 2 * K.discriminant := by
    simpa only [NumberFieldCode.discriminant] using hrelation
  have hdiscPos :
      0 < quarticDiscriminant (quarticS1 K.1 a)
        (quarticS2 K.1 a) (quarticS3 K.1 a)
        (quarticS4 K.1 a) := by
    rw [hrelation']
    exact mul_pos hsquare hfieldPos
  rcases normalize_quartic_coefficients
      (quarticS1 K.1 a) (quarticS2 K.1 a)
      (quarticS3 K.1 a) (quarticS4 K.1 a)
      hnoRoot hnoQuadratic with
    ⟨s1, s2, s3, s4, hs1, hspread, hminorEq,
      hdiscEq, hnoRootNorm, hnoQuadraticNorm⟩
  have hspreadPosNorm : 0 < quarticSpread s1 s2 := by
    rw [hspread]
    exact hspreadPos
  have hspreadLtNorm : quarticSpread s1 s2 < 29 := by
    rw [hspread]
    exact hspreadLt
  have hminorNorm :
      0 < quarticHermiteMinorThree s1 s2 s3 s4 := by
    rw [hminorEq]
    exact hminor
  have hdiscPosNorm : 0 < quarticDiscriminant s1 s2 s3 s4 := by
    rw [hdiscEq]
    exact hdiscPos
  obtain ⟨hs3, hs3', hs4, hs4'⟩ :=
    quartic_s3_s4_bounds_of_normalized
      s1 s2 s3 s4 hs1 hspreadPosNorm hspreadLtNorm
        hminorNorm hdiscPosNorm
  have hrelationNorm :
      quarticDiscriminant s1 s2 s3 s4 =
        (index : ℤ) ^ 2 * K.discriminant := by
    rw [hdiscEq]
    exact hrelation'
  exact ⟨s1, s2, s3, s4, index, hs1, hs3, hs3', hs4, hs4',
    hspreadPosNorm, hspreadLtNorm, hminorNorm, hdiscPosNorm,
    hnoRootNorm, hnoQuadraticNorm, hindex, hrelationNorm⟩

end

end TraceEuclidean
