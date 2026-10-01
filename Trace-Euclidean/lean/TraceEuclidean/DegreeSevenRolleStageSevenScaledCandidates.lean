import TraceEuclidean.DegreeSevenRolleStageSevenScaled
import TraceEuclidean.ScaledIntegerPolynomialInterval

/-!
# Cleared-denominator final coefficient intervals for degree seven

The six certified critical-point intervals share one integer denominator. This
module computes the final `a0` interval entirely in integers and proves that it
equals the rational interval used by the proof-facing Stage Seven entry.
-/

namespace TraceEuclidean

open LeanCert.Core

noncomputable section

namespace DegreeSevenStageSevenScaledEntry

def scaledBaseCoefficients
    (entry : DegreeSevenStageSevenScaledEntry) : List ℤ :=
  [0, entry.a1, entry.a2, entry.a3,
    entry.a4, entry.a5, entry.a6, 1]

def scaledRootValueRange (entry : DegreeSevenStageSevenScaledEntry)
    (lower upper : ℤ) : ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval entry.denominator lower upper
    entry.scaledBaseCoefficients

def scaledEndpointValueRange
    (entry : DegreeSevenStageSevenScaledEntry) (numerator : ℤ) : ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval 7 numerator numerator
    entry.scaledBaseCoefficients

def scaledA0LowerBound (entry : DegreeSevenStageSevenScaledEntry) : ℤ :=
  max
    (-((entry.scaledRootValueRange entry.firstLower entry.firstUpper).2 /
      entry.denominator ^ entry.scaledBaseCoefficients.length))
    (max
      (-((entry.scaledRootValueRange entry.thirdLower entry.thirdUpper).2 /
        entry.denominator ^ entry.scaledBaseCoefficients.length))
      (max
        (-((entry.scaledRootValueRange entry.fifthLower entry.fifthUpper).2 /
          entry.denominator ^ entry.scaledBaseCoefficients.length))
        (-((entry.scaledEndpointValueRange (-entry.a6 + 38)).2 /
          7 ^ entry.scaledBaseCoefficients.length))))

def scaledA0UpperBound (entry : DegreeSevenStageSevenScaledEntry) : ℤ :=
  min
    ((-(entry.scaledEndpointValueRange (-entry.a6 - 38)).1) /
      7 ^ entry.scaledBaseCoefficients.length)
    (min
      ((-(entry.scaledRootValueRange entry.secondLower entry.secondUpper).1) /
        entry.denominator ^ entry.scaledBaseCoefficients.length)
      (min
        ((-(entry.scaledRootValueRange entry.fourthLower entry.fourthUpper).1) /
          entry.denominator ^ entry.scaledBaseCoefficients.length)
        ((-(entry.scaledRootValueRange entry.sixthLower entry.sixthUpper).1) /
          entry.denominator ^ entry.scaledBaseCoefficients.length)))

def scaledA0Candidates
    (entry : DegreeSevenStageSevenScaledEntry) : Finset ℤ :=
  integerIcc entry.scaledA0LowerBound entry.scaledA0UpperBound

private theorem floor_intCast_div (n d : ℤ) (hd : 0 < d) :
    Int.floor ((n : ℚ) / (d : ℚ)) = n / d := by
  rw [Int.floor_div_cast_of_nonneg (le_of_lt hd), Int.floor_intCast]

private theorem ceil_neg_intCast_div (n d : ℤ) (hd : 0 < d) :
    Int.ceil (-((n : ℚ) / (d : ℚ))) = -(n / d) := by
  rw [Int.ceil_neg, floor_intCast_div n d hd]

private theorem floor_neg_intCast_div (n d : ℤ) (hd : 0 < d) :
    Int.floor (-((n : ℚ) / (d : ℚ))) = (-n) / d := by
  rw [show -((n : ℚ) / (d : ℚ)) = ((-n : ℤ) : ℚ) / (d : ℚ) by
    push_cast
    ring]
  exact floor_intCast_div (-n) d hd

private theorem ceil_neg_intCast_div_pow
    (n d : ℤ) (power : ℕ) (hd : 0 < d) :
    Int.ceil (-((n : ℚ) / (d : ℚ) ^ power)) =
      -(n / d ^ power) := by
  rw [← Int.cast_pow]
  exact ceil_neg_intCast_div n (d ^ power) (pow_pos hd power)

private theorem floor_neg_intCast_div_pow
    (n d : ℤ) (power : ℕ) (hd : 0 < d) :
    Int.floor (-((n : ℚ) / (d : ℚ) ^ power)) =
      (-n) / d ^ power := by
  rw [← Int.cast_pow]
  exact floor_neg_intCast_div n (d ^ power) (pow_pos hd power)

private theorem ceil_neg_div_seven_pow (n : ℤ) (power : ℕ) :
    Int.ceil (-((n : ℚ) / 7 ^ power)) =
      -(n / (7 : ℤ) ^ power) := by
  simpa using ceil_neg_intCast_div_pow n 7 power (by norm_num)

private theorem floor_neg_div_seven_pow (n : ℤ) (power : ℕ) :
    Int.floor (-((n : ℚ) / 7 ^ power)) =
      (-n) / (7 : ℤ) ^ power := by
  simpa using floor_neg_intCast_div_pow n 7 power (by norm_num)

private theorem scaledRootValueRange_correct
    (entry : DegreeSevenStageSevenScaledEntry)
    (lower upper : ℤ) (hd : 0 < entry.denominator) (hlu : lower ≤ upper) :
    let scaled := entry.scaledRootValueRange lower upper
    (integerPolynomialRootIntervalEval entry.scaledBaseCoefficients
      (entry.interval lower upper)).lo =
        (scaled.1 : ℚ) /
          entry.denominator ^ entry.scaledBaseCoefficients.length ∧
    (integerPolynomialRootIntervalEval entry.scaledBaseCoefficients
      (entry.interval lower upper)).hi =
        (scaled.2 : ℚ) /
          entry.denominator ^ entry.scaledBaseCoefficients.length := by
  unfold integerPolynomialRootIntervalEval
  apply scaledIntegerPolynomialIntervalEval_correct_of_endpoints
  · exact hd
  · have hq : (lower : ℚ) / entry.denominator ≤
        (upper : ℚ) / entry.denominator := by
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast hd)]
      exact_mod_cast hlu
    simp [DegreeSevenStageSevenScaledEntry.interval,
      RationalRootInterval.toIntervalRat, hq]
  · have hq : (lower : ℚ) / entry.denominator ≤
        (upper : ℚ) / entry.denominator := by
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast hd)]
      exact_mod_cast hlu
    simp [DegreeSevenStageSevenScaledEntry.interval,
      RationalRootInterval.toIntervalRat, hq]

private theorem scaledEndpointValueRange_correct
    (entry : DegreeSevenStageSevenScaledEntry) (numerator : ℤ) :
    let scaled := entry.scaledEndpointValueRange numerator
    (integerPolynomialIntervalEval entry.scaledBaseCoefficients
      (IntervalRat.singleton ((numerator : ℚ) / 7))).lo =
        (scaled.1 : ℚ) / 7 ^ entry.scaledBaseCoefficients.length ∧
    (integerPolynomialIntervalEval entry.scaledBaseCoefficients
      (IntervalRat.singleton ((numerator : ℚ) / 7))).hi =
        (scaled.2 : ℚ) / 7 ^ entry.scaledBaseCoefficients.length := by
  unfold integerPolynomialIntervalEval
  apply scaledIntegerPolynomialIntervalEval_correct_of_endpoints
  · norm_num
  · simp [IntervalRat.singleton]
  · simp [IntervalRat.singleton]

theorem a0Candidates_eq_scaledA0Candidates
    (entry : DegreeSevenStageSevenScaledEntry)
    (hvalid : entry.ArithmeticValid) :
    entry.toEntry.a0Candidates = entry.scaledA0Candidates := by
  rcases hvalid with
    ⟨hd, hfirst, hsecond, hthird, hfourth, hfifth, hsixth, _⟩
  have hfirstEval := entry.scaledRootValueRange_correct
    entry.firstLower entry.firstUpper hd hfirst.le
  have hsecondEval := entry.scaledRootValueRange_correct
    entry.secondLower entry.secondUpper hd hsecond.le
  have hthirdEval := entry.scaledRootValueRange_correct
    entry.thirdLower entry.thirdUpper hd hthird.le
  have hfourthEval := entry.scaledRootValueRange_correct
    entry.fourthLower entry.fourthUpper hd hfourth.le
  have hfifthEval := entry.scaledRootValueRange_correct
    entry.fifthLower entry.fifthUpper hd hfifth.le
  have hsixthEval := entry.scaledRootValueRange_correct
    entry.sixthLower entry.sixthUpper hd hsixth.le
  have hleftEval := entry.scaledEndpointValueRange_correct (-entry.a6 - 38)
  have hrightEval := entry.scaledEndpointValueRange_correct (-entry.a6 + 38)
  have hleftEndpoint :
      (-(entry.a6 : ℚ) - 38) / 7 =
        ((-entry.a6 - 38 : ℤ) : ℚ) / 7 := by
    push_cast
    ring
  have hrightEndpoint :
      (-(entry.a6 : ℚ) + 38) / 7 =
        ((-entry.a6 + 38 : ℤ) : ℚ) / 7 := by
    push_cast
    ring
  unfold DegreeSevenStageSevenEntry.a0Candidates
    septicTranslationCandidates
    septicTranslationLowerBound septicTranslationUpperBound
    scaledA0Candidates scaledA0LowerBound scaledA0UpperBound
  simp only [DegreeSevenStageSevenScaledEntry.toEntry,
    DegreeSevenStageSevenEntry.baseCoefficients,
    DegreeSevenStageSevenEntry.leftEndpoint,
    DegreeSevenStageSevenEntry.rightEndpoint,
    hleftEndpoint, hrightEndpoint]
  change integerIcc _ _ = integerIcc _ _
  congr 1
  · rw [show [0, entry.a1, entry.a2, entry.a3,
        entry.a4, entry.a5, entry.a6, 1] =
        entry.scaledBaseCoefficients by rfl]
    rw [hfirstEval.2, hthirdEval.2, hfifthEval.2, hrightEval.2]
    rw [ceil_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.firstLower entry.firstUpper).2
        entry.denominator entry.scaledBaseCoefficients.length hd,
      ceil_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.thirdLower entry.thirdUpper).2
        entry.denominator entry.scaledBaseCoefficients.length hd,
      ceil_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.fifthLower entry.fifthUpper).2
        entry.denominator entry.scaledBaseCoefficients.length hd,
      ceil_neg_div_seven_pow
        (entry.scaledEndpointValueRange (-entry.a6 + 38)).2
        entry.scaledBaseCoefficients.length]
  · rw [show [0, entry.a1, entry.a2, entry.a3,
        entry.a4, entry.a5, entry.a6, 1] =
        entry.scaledBaseCoefficients by rfl]
    rw [hleftEval.1, hsecondEval.1, hfourthEval.1, hsixthEval.1]
    rw [floor_neg_div_seven_pow
        (entry.scaledEndpointValueRange (-entry.a6 - 38)).1
        entry.scaledBaseCoefficients.length,
      floor_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.secondLower entry.secondUpper).1
        entry.denominator entry.scaledBaseCoefficients.length hd,
      floor_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.fourthLower entry.fourthUpper).1
        entry.denominator entry.scaledBaseCoefficients.length hd,
      floor_neg_intCast_div_pow
        (entry.scaledRootValueRange entry.sixthLower entry.sixthUpper).1
        entry.denominator entry.scaledBaseCoefficients.length hd]

end DegreeSevenStageSevenScaledEntry

end

end TraceEuclidean
