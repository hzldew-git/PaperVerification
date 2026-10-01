import TraceEuclidean.DegreeSevenRolleStageSevenRejected
import TraceEuclidean.DegreeSevenRolleStageSixScaledFamily
import TraceEuclidean.ScaledIntegerPolynomialInterval

/-!
# Scaled critical-sign rejection certificates for Stage Seven

Generated data stores the five critical-point intervals with a common integer
denominator.  This module converts the integer-checkable parent certificate
and one exact interval sign contradiction into the proof-facing rejection
witness used by the final degree-seven Rolle stage.
-/

namespace TraceEuclidean

noncomputable section

/-- A generated critical-sign rejection record with a scaled Stage Six
parent. -/
structure DegreeSevenStageSevenScaledCriticalSignWitness where
  parent : DegreeSevenStageSixScaledFamily
  a2 : ℤ
  a1 : ℤ
  point : DegreeSevenStageSevenCriticalPoint
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenScaledCriticalSignWitness

namespace CriticalPoint

def scaledLower (point : DegreeSevenStageSevenCriticalPoint)
    (parent : DegreeSevenStageSixScaledFamily) : ℤ :=
  match point with
  | .first => parent.firstLower
  | .second => parent.secondLower
  | .third => parent.thirdLower
  | .fourth => parent.fourthLower
  | .fifth => parent.fifthLower

def scaledUpper (point : DegreeSevenStageSevenCriticalPoint)
    (parent : DegreeSevenStageSixScaledFamily) : ℤ :=
  match point with
  | .first => parent.firstUpper
  | .second => parent.secondUpper
  | .third => parent.thirdUpper
  | .fourth => parent.fourthUpper
  | .fifth => parent.fifthUpper

end CriticalPoint

def toWitness
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness) :
    DegreeSevenStageSevenCriticalSignWitness where
  parent := witness.parent.toFamily.toEntry witness.a2
  a1 := witness.a1
  point := witness.point

/-- Integer numerators for the critical-value interval after clearing the
common denominator to the length of the dense coefficient list. -/
def scaledCriticalValueRange
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness) :
    ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval witness.parent.denominator
    (CriticalPoint.scaledLower witness.point witness.parent)
    (CriticalPoint.scaledUpper witness.point witness.parent)
    witness.toWitness.coefficients

/-- All generated obligations: the scaled parent is valid, `a2` lies in its
parameter interval, and the selected critical interval has the forbidden
strict sign. -/
def ArithmeticValid
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness) : Prop :=
  witness.parent.ArithmeticValid ∧
    witness.parent.a2Lower ≤ witness.a2 ∧
    witness.a2 ≤ witness.parent.a2Upper ∧
    match witness.point with
    | .first => 0 < witness.scaledCriticalValueRange.1
    | .second => witness.scaledCriticalValueRange.2 < 0
    | .third => 0 < witness.scaledCriticalValueRange.1
    | .fourth => witness.scaledCriticalValueRange.2 < 0
    | .fifth => 0 < witness.scaledCriticalValueRange.1

instance (witness : DegreeSevenStageSevenScaledCriticalSignWitness) :
    Decidable witness.ArithmeticValid := by
  unfold ArithmeticValid
  cases witness.point <;> infer_instance

private theorem scaledInterval_order
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness)
    (hparent : witness.parent.ArithmeticValid) :
    CriticalPoint.scaledLower witness.point witness.parent <
      CriticalPoint.scaledUpper witness.point witness.parent := by
  rcases hparent with
    ⟨_, _, hfirst, hsecond, hthird, hfourth, hfifth, _⟩
  cases witness.point <;>
    simp only [CriticalPoint.scaledLower, CriticalPoint.scaledUpper] <;>
    assumption

private theorem criticalValueRange_endpoints
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness)
    (hparent : witness.parent.ArithmeticValid) :
    witness.toWitness.criticalValueRange.lo =
        (witness.scaledCriticalValueRange.1 : ℚ) /
          witness.parent.denominator ^ witness.toWitness.coefficients.length ∧
      witness.toWitness.criticalValueRange.hi =
        (witness.scaledCriticalValueRange.2 : ℚ) /
          witness.parent.denominator ^ witness.toWitness.coefficients.length := by
  have hdenominator : 0 < witness.parent.denominator := hparent.1
  have hdenominatorRat : (0 : ℚ) < witness.parent.denominator := by
    exact_mod_cast hdenominator
  have horder := scaledInterval_order witness hparent
  have horderRat :
      (CriticalPoint.scaledLower witness.point witness.parent : ℚ) /
          witness.parent.denominator ≤
        (CriticalPoint.scaledUpper witness.point witness.parent : ℚ) /
          witness.parent.denominator := by
    rw [div_le_div_iff_of_pos_right hdenominatorRat]
    exact_mod_cast horder.le
  have hinterval :
      witness.point.interval witness.toWitness.parent =
        witness.parent.interval
          (CriticalPoint.scaledLower witness.point witness.parent)
          (CriticalPoint.scaledUpper witness.point witness.parent) := by
    cases witness.point <;> rfl
  have hinputLower :
      (witness.point.interval witness.toWitness.parent).toIntervalRat.lo =
        (CriticalPoint.scaledLower witness.point witness.parent : ℚ) /
          witness.parent.denominator := by
    rw [hinterval]
    simp [DegreeSevenStageSixScaledFamily.interval,
      RationalRootInterval.toIntervalRat, horderRat]
  have hinputUpper :
      (witness.point.interval witness.toWitness.parent).toIntervalRat.hi =
        (CriticalPoint.scaledUpper witness.point witness.parent : ℚ) /
          witness.parent.denominator := by
    rw [hinterval]
    simp [DegreeSevenStageSixScaledFamily.interval,
      RationalRootInterval.toIntervalRat, horderRat]
  simpa [DegreeSevenStageSevenCriticalSignWitness.criticalValueRange,
      integerPolynomialRootIntervalEval, scaledCriticalValueRange,
      toWitness] using
    scaledIntegerPolynomialIntervalEval_correct_of_endpoints
      witness.toWitness.coefficients
      (witness.point.interval witness.toWitness.parent).toIntervalRat
      witness.parent.denominator
      (CriticalPoint.scaledLower witness.point witness.parent)
      (CriticalPoint.scaledUpper witness.point witness.parent)
      hdenominator hinputLower hinputUpper

/-- Integer and rational arithmetic validity supplies the mathematical
critical-sign rejection witness. -/
theorem valid_of_arithmeticValid
    (witness : DegreeSevenStageSevenScaledCriticalSignWitness)
    (hvalid : witness.ArithmeticValid) : witness.toWitness.Valid := by
  rcases hvalid with ⟨hparent, ha2Lower, ha2Upper, hsign⟩
  have hrange := criticalValueRange_endpoints witness hparent
  have hdenominatorRat : (0 : ℚ) < witness.parent.denominator := by
    exact_mod_cast hparent.1
  have hpower :
      (0 : ℚ) < witness.parent.denominator ^
        witness.toWitness.coefficients.length := by
    positivity
  refine ⟨?_, ?_⟩
  · exact DegreeSevenStageSixFamily.toEntry_valid witness.parent.toFamily
      (DegreeSevenStageSixScaledFamily.valid_of_arithmeticValid
        witness.parent hparent) ha2Lower ha2Upper
  · cases hpoint : witness.point <;>
      simp only [toWitness, hpoint] at hsign hrange ⊢
    · rw [hrange.1]
      have hsignRat :
          (0 : ℚ) < (witness.scaledCriticalValueRange.1 : ℚ) := by
        exact_mod_cast hsign
      exact div_pos hsignRat hpower
    · rw [hrange.2]
      have hsignRat :
          (witness.scaledCriticalValueRange.2 : ℚ) < 0 := by
        exact_mod_cast hsign
      exact div_neg_of_neg_of_pos hsignRat hpower
    · rw [hrange.1]
      have hsignRat :
          (0 : ℚ) < (witness.scaledCriticalValueRange.1 : ℚ) := by
        exact_mod_cast hsign
      exact div_pos hsignRat hpower
    · rw [hrange.2]
      have hsignRat :
          (witness.scaledCriticalValueRange.2 : ℚ) < 0 := by
        exact_mod_cast hsign
      exact div_neg_of_neg_of_pos hsignRat hpower
    · rw [hrange.1]
      have hsignRat :
          (0 : ℚ) < (witness.scaledCriticalValueRange.1 : ℚ) := by
        exact_mod_cast hsign
      exact div_pos hsignRat hpower

end DegreeSevenStageSevenScaledCriticalSignWitness

end

end TraceEuclidean
