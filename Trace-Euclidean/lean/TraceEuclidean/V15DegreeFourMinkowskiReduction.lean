import TraceEuclidean.V15DegreeFourHunterReduction
import TraceEuclidean.V15QuarticOrderMaximality2304

/-!
# Degree-four reduction using the unconditional Minkowski ball

The three-dimensional Minkowski ball supplies a projected nonzero vector with
scaled squared norm below `35`.  Maximality of the `2048` and `2304` power
orders now closes every arithmetic row that can arise from a primitive lift.
This module isolates the sole remaining step in this route: choosing such a
short vector whose lift generates the quartic field.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped NumberField

open scoped Classical in
/-- The remaining selection statement for the unconditional spread-`35`
route.  Starting from the nonzero projected vector supplied by Minkowski, it
selects a vector with the same bound whose algebraic-integer lift generates
the quartic field. -/
def V15QuarticPrimitiveShortSelectionThirtyFiveInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K.1)),
      ((((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) =
          v15EuclideanOne K.1) →
      (∃ x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        4 * ‖((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35) →
      ∃ x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ),
        x ≠ 0 ∧
        IntermediateField.adjoin ℚ
          {((v15QuarticHunterAlgebraicIntegerLift K.1 bz x : 𝓞 K.1) :
            K.1)} = ⊤ ∧
        4 * ‖((x : v15QuarticHunterProjectedLattice
          (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 2 < 35

/-- Primitive-generator form of the remaining spread-`35` selection input. -/
def V15DegreeFourPrimitiveGeneratorThirtyFiveInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
      ∃ a : 𝓞 K.1,
        IntermediateField.adjoin ℚ {((a : 𝓞 K.1) : K.1)} = ⊤ ∧
        v15QuarticSpread (v15QuarticS1 K.1 a)
          (v15QuarticS2 K.1 a) < 35

set_option maxHeartbeats 0 in
-- Rewriting the dependent orthogonal-complement type after fixing the first
-- basis vector requires additional reduction.
open scoped Classical in
/-- The unconditional Minkowski short-vector theorem and the spread-`35`
selection statement produce an actual primitive quartic generator. -/
theorem v15_degree_four_primitiveGenerator_thirtyFive_of_selection
    (hSelection : V15QuarticPrimitiveShortSelectionThirtyFiveInput) :
    V15DegreeFourPrimitiveGeneratorThirtyFiveInput := by
  intro K hreal hdegree hdisc
  have hdisc' : |NumberField.discr K.1| < 725 := by
    simpa only [NumberFieldCode.discriminant] using hdisc
  obtain ⟨bz, hbzero, x, hx, hshort⟩ :=
    v15_quartic_projected_shortVector_minkowski
      K.1 hreal hdegree hdisc'
  obtain ⟨y, hy, hgen, hshort'⟩ :=
    hSelection K hreal hdegree hdisc bz hbzero ⟨x, hx, hshort⟩
  let a : 𝓞 K.1 := v15QuarticHunterAlgebraicIntegerLift K.1 bz y
  change IntermediateField.adjoin ℚ {(a : K.1)} = ⊤ at hgen
  refine ⟨a, hgen, ?_⟩
  have hbzero' : (bz.ofZLatticeBasis ℝ) 0 =
      v15EuclideanOne K.1 := by
    rw [show (bz.ofZLatticeBasis ℝ) 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K.1) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K.1)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K.1) 0]
    exact hbzero
  have he : inner ℝ (v15EuclideanOne K.1)
      (v15EuclideanOne K.1) ≠ 0 := by
    rw [v15_inner_euclideanOne_self_eq_four K.1 hreal hdegree]
    norm_num
  have hshortBasis :
      4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
          (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
      (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
      ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
        (NumberField.mixedEmbedding K.1
          ((v15QuarticHunterAlgebraicIntegerLift K.1 bz y : 𝓞 K.1) :
            K.1)))‖ ^ 2 < 35
    rw [v15_quarticHunterAlgebraicIntegerLift_center K.1 bz y]
    exact hshort'
  have hshortCenter :
      4 * ‖v15HunterCenterLinearMap (v15EuclideanOne K.1) he
        (v15EuclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 35 := by
    change 4 * ‖v15HunterCenter (v15EuclideanOne K.1)
      (v15EuclideanEmbedding K.1 (a : K.1))‖ ^ 2 < 35
    change 4 * ‖v15HunterCenter ((bz.ofZLatticeBasis ℝ) 0)
      ((NumberField.mixedEmbedding.euclidean.toMixed K.1).symm
        (NumberField.mixedEmbedding K.1 (a : K.1)))‖ ^ 2 < 35 at hshortBasis
    rw [hbzero'] at hshortBasis
    unfold v15EuclideanEmbedding at ⊢
    exact hshortBasis
  have hspread := v15_quarticSpread_cast_eq_center_norm
    K.1 hreal hdegree a hgen he
  have hspreadReal :
      ((v15QuarticSpread (v15QuarticS1 K.1 a)
        (v15QuarticS2 K.1 a) : ℤ) : ℝ) < 35 := by
    rw [hspread]
    exact hshortCenter
  exact_mod_cast hspreadReal

/-- The ordinary totally-real Minkowski bound already puts every quartic
field discriminant strictly above `29`. -/
theorem v15_totallyReal_quartic_discriminant_gt_twentyNine
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4) :
    29 < NumberField.discr K := by
  letI : NumberField.IsTotallyReal K := hreal
  have hsign : (NumberField.discr K).sign = 1 := by
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hpos : 0 < NumberField.discr K :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hbound := NumberField.abs_discr_ge' K
  rw [hdegree, NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at hbound
  have hrealLower : (29 : ℝ) < ((|NumberField.discr K| : ℤ) : ℝ) := by
    calc
      (29 : ℝ) < (4 : ℝ) ^ (2 * 4) /
          ((4 / Real.pi) ^ (2 * 0) * (Nat.factorial 4 : ℝ) ^ 2) := by
        norm_num
      _ ≤ ((|NumberField.discr K| : ℤ) : ℝ) := hbound
  rw [abs_of_pos hpos] at hrealLower
  exact_mod_cast hrealLower

/-- Once the spread-`35` selection statement is supplied, the unconditional
Minkowski route proves the quartic field-discriminant lower bound `725`. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_minkowski_selection
    (hSelection : V15QuarticPrimitiveShortSelectionThirtyFiveInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  by_contra hnot
  have hdisc : |K.discriminant| < 725 := by omega
  obtain ⟨a, hgen, hspread⟩ :=
    v15_degree_four_primitiveGenerator_thirtyFive_of_selection
      hSelection K hreal hdegree hdisc
  letI : NumberField.IsTotallyReal K.1 := hreal
  have hsign : (NumberField.discr K.1).sign = 1 := by
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hpos : 0 < NumberField.discr K.1 :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hupper : NumberField.discr K.1 < 725 := by
    simpa only [NumberFieldCode.discriminant, abs_of_pos hpos] using hdisc
  have hlower : 29 < NumberField.discr K.1 :=
    v15_totallyReal_quartic_discriminant_gt_twentyNine
      K.1 hreal hdegree
  exact v15_quartic_weak_minkowski_contradiction
    K.1 hreal hdegree a hgen hspread hlower hupper

end

end TraceEuclidean
