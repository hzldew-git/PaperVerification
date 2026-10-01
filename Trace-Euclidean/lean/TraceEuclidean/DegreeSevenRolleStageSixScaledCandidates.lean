import TraceEuclidean.DegreeSevenRolleStageSixScaledFamily
import TraceEuclidean.ScaledIntegerPolynomialInterval

namespace TraceEuclidean
open LeanCert.Core
noncomputable section

namespace DegreeSevenStageSixScaledFamily

def scaledBaseCoefficients (family : DegreeSevenStageSixScaledFamily)
    (a2 : ℤ) : List ℤ :=
  [0, 2 * a2, 3 * family.a3, 4 * family.a4,
    5 * family.a5, 6 * family.a6, 7]

def scaledRootValueRange (family : DegreeSevenStageSixScaledFamily)
    (a2 lower upper : ℤ) : ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval family.denominator lower upper
    (family.scaledBaseCoefficients a2)

def scaledEndpointValueRange (family : DegreeSevenStageSixScaledFamily)
    (a2 numerator : ℤ) : ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval 7 numerator numerator
    (family.scaledBaseCoefficients a2)

def scaledA1LowerBound (family : DegreeSevenStageSixScaledFamily)
    (a2 : ℤ) : ℤ :=
  max
    (-((family.scaledEndpointValueRange a2 (-family.a6 - 38)).2 /
      7 ^ (family.scaledBaseCoefficients a2).length))
    (max
      (-((family.scaledRootValueRange a2 family.secondLower
        family.secondUpper).2 /
          family.denominator ^ (family.scaledBaseCoefficients a2).length))
      (max
        (-((family.scaledRootValueRange a2 family.fourthLower
          family.fourthUpper).2 /
            family.denominator ^ (family.scaledBaseCoefficients a2).length))
        (-((family.scaledEndpointValueRange a2 (-family.a6 + 38)).2 /
          7 ^ (family.scaledBaseCoefficients a2).length))))

def scaledA1UpperBound (family : DegreeSevenStageSixScaledFamily)
    (a2 : ℤ) : ℤ :=
  min
    ((-(family.scaledRootValueRange a2 family.firstLower
      family.firstUpper).1) /
        family.denominator ^ (family.scaledBaseCoefficients a2).length)
    (min
      ((-(family.scaledRootValueRange a2 family.thirdLower
        family.thirdUpper).1) /
          family.denominator ^ (family.scaledBaseCoefficients a2).length)
      ((-(family.scaledRootValueRange a2 family.fifthLower
        family.fifthUpper).1) /
          family.denominator ^ (family.scaledBaseCoefficients a2).length))

def scaledA1Candidates (family : DegreeSevenStageSixScaledFamily)
    (a2 : ℤ) : Finset ℤ :=
  integerIcc (family.scaledA1LowerBound a2)
    (family.scaledA1UpperBound a2)

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

private theorem scaledRootValueRange_correct
    (family : DegreeSevenStageSixScaledFamily)
    (a2 lower upper : ℤ) (hd : 0 < family.denominator)
    (hlu : lower ≤ upper) :
    let scaled := family.scaledRootValueRange a2 lower upper
    (integerPolynomialRootIntervalEval
      (family.scaledBaseCoefficients a2)
      (family.interval lower upper)).lo =
        (scaled.1 : ℚ) /
          family.denominator ^ (family.scaledBaseCoefficients a2).length ∧
    (integerPolynomialRootIntervalEval
      (family.scaledBaseCoefficients a2)
      (family.interval lower upper)).hi =
        (scaled.2 : ℚ) /
          family.denominator ^ (family.scaledBaseCoefficients a2).length := by
  unfold integerPolynomialRootIntervalEval
  apply scaledIntegerPolynomialIntervalEval_correct_of_endpoints
  · exact hd
  · have hq : (lower : ℚ) / family.denominator ≤
        (upper : ℚ) / family.denominator := by
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast hd)]
      exact_mod_cast hlu
    simp [DegreeSevenStageSixScaledFamily.interval,
      RationalRootInterval.toIntervalRat, hq]
  · have hq : (lower : ℚ) / family.denominator ≤
        (upper : ℚ) / family.denominator := by
      rw [div_le_div_iff_of_pos_right (by exact_mod_cast hd)]
      exact_mod_cast hlu
    simp [DegreeSevenStageSixScaledFamily.interval,
      RationalRootInterval.toIntervalRat, hq]

private theorem scaledEndpointValueRange_correct
    (family : DegreeSevenStageSixScaledFamily)
    (a2 numerator : ℤ) :
    let scaled := family.scaledEndpointValueRange a2 numerator
    (integerPolynomialIntervalEval
      (family.scaledBaseCoefficients a2)
      (IntervalRat.singleton ((numerator : ℚ) / 7))).lo =
        (scaled.1 : ℚ) /
          7 ^ (family.scaledBaseCoefficients a2).length ∧
    (integerPolynomialIntervalEval
      (family.scaledBaseCoefficients a2)
      (IntervalRat.singleton ((numerator : ℚ) / 7))).hi =
        (scaled.2 : ℚ) /
          7 ^ (family.scaledBaseCoefficients a2).length := by
  unfold integerPolynomialIntervalEval
  apply scaledIntegerPolynomialIntervalEval_correct_of_endpoints
  · norm_num
  · simp [IntervalRat.singleton]
  · simp [IntervalRat.singleton]

theorem a1Candidates_eq_scaledA1Candidates
    (family : DegreeSevenStageSixScaledFamily) (a2 : ℤ)
    (hvalid : family.ArithmeticValid) :
    (family.toFamily.toEntry a2).a1Candidates =
      family.scaledA1Candidates a2 := by
  rcases hvalid with
    ⟨hd, _, hfirst, hsecond, hthird, hfourth, hfifth, _⟩
  have hfirstEval := family.scaledRootValueRange_correct a2
    family.firstLower family.firstUpper hd hfirst.le
  have hsecondEval := family.scaledRootValueRange_correct a2
    family.secondLower family.secondUpper hd hsecond.le
  have hthirdEval := family.scaledRootValueRange_correct a2
    family.thirdLower family.thirdUpper hd hthird.le
  have hfourthEval := family.scaledRootValueRange_correct a2
    family.fourthLower family.fourthUpper hd hfourth.le
  have hfifthEval := family.scaledRootValueRange_correct a2
    family.fifthLower family.fifthUpper hd hfifth.le
  have hleftEval := family.scaledEndpointValueRange_correct a2
    (-family.a6 - 38)
  have hrightEval := family.scaledEndpointValueRange_correct a2
    (-family.a6 + 38)
  have hleftEndpoint :
      (-(family.a6 : ℚ) - 38) / 7 =
        ((-family.a6 - 38 : ℤ) : ℚ) / 7 := by
    push_cast
    ring
  have hrightEndpoint :
      (-(family.a6 : ℚ) + 38) / 7 =
        ((-family.a6 + 38 : ℤ) : ℚ) / 7 := by
    push_cast
    ring
  unfold DegreeSevenStageSixEntry.a1Candidates
    sexticTranslationCandidates
    sexticTranslationLowerBound sexticTranslationUpperBound
    scaledA1Candidates scaledA1LowerBound scaledA1UpperBound
  simp only [DegreeSevenStageSixFamily.toEntry,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixEntry.baseCoefficients,
    DegreeSevenStageSixEntry.leftEndpoint,
    DegreeSevenStageSixEntry.rightEndpoint,
    hleftEndpoint, hrightEndpoint]
  change integerIcc _ _ = integerIcc _ _
  congr 1
  · rw [show [0, 2 * a2, 3 * family.a3, 4 * family.a4,
        5 * family.a5, 6 * family.a6, 7] =
        family.scaledBaseCoefficients a2 by rfl]
    rw [hleftEval.2, hsecondEval.2, hfourthEval.2, hrightEval.2]
    rw [ceil_neg_div_seven_pow
        (family.scaledEndpointValueRange a2 (-family.a6 - 38)).2
        (family.scaledBaseCoefficients a2).length,
      ceil_neg_intCast_div_pow
        (family.scaledRootValueRange a2 family.secondLower
          family.secondUpper).2 family.denominator
        (family.scaledBaseCoefficients a2).length hd,
      ceil_neg_intCast_div_pow
        (family.scaledRootValueRange a2 family.fourthLower
          family.fourthUpper).2 family.denominator
        (family.scaledBaseCoefficients a2).length hd,
      ceil_neg_div_seven_pow
        (family.scaledEndpointValueRange a2 (-family.a6 + 38)).2
        (family.scaledBaseCoefficients a2).length]
  · rw [show [0, 2 * a2, 3 * family.a3, 4 * family.a4,
        5 * family.a5, 6 * family.a6, 7] =
        family.scaledBaseCoefficients a2 by rfl]
    rw [hfirstEval.1, hthirdEval.1, hfifthEval.1]
    rw [floor_neg_intCast_div_pow
        (family.scaledRootValueRange a2 family.firstLower
          family.firstUpper).1 family.denominator
        (family.scaledBaseCoefficients a2).length hd,
      floor_neg_intCast_div_pow
        (family.scaledRootValueRange a2 family.thirdLower
          family.thirdUpper).1 family.denominator
        (family.scaledBaseCoefficients a2).length hd,
      floor_neg_intCast_div_pow
        (family.scaledRootValueRange a2 family.fifthLower
          family.fifthUpper).1 family.denominator
        (family.scaledBaseCoefficients a2).length hd]
end DegreeSevenStageSixScaledFamily
end
end TraceEuclidean
