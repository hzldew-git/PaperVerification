import TraceEuclidean.DegreeSevenRolleStageSixFamily

/-!
# Variable-precision parametric certificates for the sixth Rolle stage

The fixed `65536` denominator used by the compact coarse frontier is adequate
for completeness.  Later coefficient filtering needs narrower intervals.  A
scaled family stores one arbitrary positive common denominator and checks all
uniform root signs after clearing its fifth power.
-/

namespace TraceEuclidean

noncomputable section

/-- A variable-precision five-root certificate for an interval of `a2`. -/
structure DegreeSevenStageSixScaledFamily where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2Lower : ℤ
  a2Upper : ℤ
  denominator : ℤ
  firstLower : ℤ
  firstUpper : ℤ
  secondLower : ℤ
  secondUpper : ℤ
  thirdLower : ℤ
  thirdUpper : ℤ
  fourthLower : ℤ
  fourthUpper : ℤ
  fifthLower : ℤ
  fifthUpper : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageSixScaledFamily

def interval (family : DegreeSevenStageSixScaledFamily)
    (lower upper : ℤ) : RationalRootInterval where
  lower := (lower : ℚ) / family.denominator
  upper := (upper : ℚ) / family.denominator

def toFamily (family : DegreeSevenStageSixScaledFamily) :
    DegreeSevenStageSixFamily where
  a6 := family.a6
  a5 := family.a5
  a4 := family.a4
  a3 := family.a3
  a2Lower := family.a2Lower
  a2Upper := family.a2Upper
  firstRoot := family.interval family.firstLower family.firstUpper
  secondRoot := family.interval family.secondLower family.secondUpper
  thirdRoot := family.interval family.thirdLower family.thirdUpper
  fourthRoot := family.interval family.fourthLower family.fourthUpper
  fifthRoot := family.interval family.fifthLower family.fifthUpper

/-- Numerator of the quintic value after clearing `denominator ^ 5`. -/
def scaledNumerator (family : DegreeSevenStageSixScaledFamily)
    (a2 cell : ℤ) : ℤ :=
  a2 * family.denominator ^ 5 +
    (3 * family.a3) * cell * family.denominator ^ 4 +
    (6 * family.a4) * cell ^ 2 * family.denominator ^ 3 +
    (10 * family.a5) * cell ^ 3 * family.denominator ^ 2 +
    (15 * family.a6) * cell ^ 4 * family.denominator +
    21 * cell ^ 5

/-- Pure integer form of the uniform signs, interval orders, and separation. -/
def ArithmeticValid (family : DegreeSevenStageSixScaledFamily) : Prop :=
  0 < family.denominator ∧
    family.a2Lower ≤ family.a2Upper ∧
    family.firstLower < family.firstUpper ∧
    family.secondLower < family.secondUpper ∧
    family.thirdLower < family.thirdUpper ∧
    family.fourthLower < family.fourthUpper ∧
    family.fifthLower < family.fifthUpper ∧
    family.scaledNumerator family.a2Upper family.firstLower < 0 ∧
    0 < family.scaledNumerator family.a2Lower family.firstUpper ∧
    0 < family.scaledNumerator family.a2Lower family.secondLower ∧
    family.scaledNumerator family.a2Upper family.secondUpper < 0 ∧
    family.scaledNumerator family.a2Upper family.thirdLower < 0 ∧
    0 < family.scaledNumerator family.a2Lower family.thirdUpper ∧
    0 < family.scaledNumerator family.a2Lower family.fourthLower ∧
    family.scaledNumerator family.a2Upper family.fourthUpper < 0 ∧
    family.scaledNumerator family.a2Upper family.fifthLower < 0 ∧
    0 < family.scaledNumerator family.a2Lower family.fifthUpper ∧
    family.firstUpper < family.secondLower ∧
    family.secondUpper < family.thirdLower ∧
    family.thirdUpper < family.fourthLower ∧
    family.fourthUpper < family.fifthLower

instance (family : DegreeSevenStageSixScaledFamily) :
    Decidable family.ArithmeticValid := by
  unfold ArithmeticValid scaledNumerator
  infer_instance

def Valid (family : DegreeSevenStageSixScaledFamily) : Prop :=
  family.toFamily.Valid

theorem rationalEval_eq_scaledNumerator_div
    (family : DegreeSevenStageSixScaledFamily)
    (a2 cell : ℤ) (hdenominator : family.denominator ≠ 0) :
    integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / family.denominator) =
      (family.scaledNumerator a2 cell : ℚ) /
        family.denominator ^ 5 := by
  simp [integerPolynomialRationalEval, DensePolynomial.eval,
    scaledNumerator]
  field_simp [hdenominator]
  ring

private theorem scaledEval_neg
    (family : DegreeSevenStageSixScaledFamily)
    (a2 cell : ℤ) (hdenominator : 0 < family.denominator)
    (h : family.scaledNumerator a2 cell < 0) :
    integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / family.denominator) < 0 := by
  rw [rationalEval_eq_scaledNumerator_div _ _ _
    (ne_of_gt hdenominator)]
  apply div_neg_of_neg_of_pos
  · exact_mod_cast h
  · positivity

private theorem scaledEval_pos
    (family : DegreeSevenStageSixScaledFamily)
    (a2 cell : ℤ) (hdenominator : 0 < family.denominator)
    (h : 0 < family.scaledNumerator a2 cell) :
    0 < integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / family.denominator) := by
  rw [rationalEval_eq_scaledNumerator_div _ _ _
    (ne_of_gt hdenominator)]
  apply div_pos
  · exact_mod_cast h
  · positivity

private theorem scaledCell_lt
    (family : DegreeSevenStageSixScaledFamily)
    (x y : ℤ) (hdenominator : 0 < family.denominator) (h : x < y) :
    (x : ℚ) / family.denominator < (y : ℚ) / family.denominator := by
  rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hdenominator)]
  exact_mod_cast h

/-- Integer arithmetic validity implies the proof-facing parametric root
certificate. -/
theorem valid_of_arithmeticValid
    (family : DegreeSevenStageSixScaledFamily)
    (h : family.ArithmeticValid) : family.Valid := by
  rcases h with
    ⟨hdenominator, ha2, hfirstInterval, hsecondInterval, hthirdInterval,
      hfourthInterval, hfifthInterval, hfirstLower, hfirstUpper,
      hsecondLower, hsecondUpper, hthirdLower, hthirdUpper, hfourthLower,
      hfourthUpper, hfifthLower, hfifthUpper, h12, h23, h34, h45⟩
  unfold Valid DegreeSevenStageSixFamily.Valid
  refine ⟨ha2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scaledCell_lt family _ _ hdenominator hfirstInterval
  · exact scaledCell_lt family _ _ hdenominator hsecondInterval
  · exact scaledCell_lt family _ _ hdenominator hthirdInterval
  · exact scaledCell_lt family _ _ hdenominator hfourthInterval
  · exact scaledCell_lt family _ _ hdenominator hfifthInterval
  · exact ⟨scaledEval_neg family _ _ hdenominator hfirstLower,
      scaledEval_pos family _ _ hdenominator hfirstUpper⟩
  · exact ⟨scaledEval_pos family _ _ hdenominator hsecondLower,
      scaledEval_neg family _ _ hdenominator hsecondUpper⟩
  · exact ⟨scaledEval_neg family _ _ hdenominator hthirdLower,
      scaledEval_pos family _ _ hdenominator hthirdUpper⟩
  · exact ⟨scaledEval_pos family _ _ hdenominator hfourthLower,
      scaledEval_neg family _ _ hdenominator hfourthUpper⟩
  · exact ⟨scaledEval_neg family _ _ hdenominator hfifthLower,
      scaledEval_pos family _ _ hdenominator hfifthUpper⟩
  · exact scaledCell_lt family _ _ hdenominator h12
  · exact scaledCell_lt family _ _ hdenominator h23
  · exact scaledCell_lt family _ _ hdenominator h34
  · exact scaledCell_lt family _ _ hdenominator h45

end DegreeSevenStageSixScaledFamily

end

end TraceEuclidean
