import TraceEuclidean.DegreeSevenRolleStageSixFamily

/-!
# Compact parametric certificates for the sixth degree-seven Rolle stage

Generated families use dyadic endpoints with denominator `65536`.  Their
validity is checked after clearing the fifth power of the denominator, so the
large finite data layer reduces only integer expressions inside Lean's kernel.
-/

namespace TraceEuclidean

noncomputable section

/-- Common denominator for compact parametric quintic root intervals. -/
def degreeSevenStageSixFamilyDenominator : ℕ := 65536

/-- A rational interval represented by two integer cells. -/
def degreeSevenStageSixFamilyInterval
    (lowerCell upperCell : ℤ) : RationalRootInterval where
  lower := (lowerCell : ℚ) / degreeSevenStageSixFamilyDenominator
  upper := (upperCell : ℚ) / degreeSevenStageSixFamilyDenominator

/-- Compact generated representation of one parametric Stage Six family. -/
structure DegreeSevenStageSixDyadicFamily where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2Lower : ℤ
  a2Upper : ℤ
  firstLowerCell : ℤ
  firstUpperCell : ℤ
  secondLowerCell : ℤ
  secondUpperCell : ℤ
  thirdLowerCell : ℤ
  thirdUpperCell : ℤ
  fourthLowerCell : ℤ
  fourthUpperCell : ℤ
  fifthLowerCell : ℤ
  fifthUpperCell : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageSixDyadicFamily

/-- Expand the integer-grid representation into the proof-facing family. -/
def toFamily (family : DegreeSevenStageSixDyadicFamily) :
    DegreeSevenStageSixFamily where
  a6 := family.a6
  a5 := family.a5
  a4 := family.a4
  a3 := family.a3
  a2Lower := family.a2Lower
  a2Upper := family.a2Upper
  firstRoot := degreeSevenStageSixFamilyInterval
    family.firstLowerCell family.firstUpperCell
  secondRoot := degreeSevenStageSixFamilyInterval
    family.secondLowerCell family.secondUpperCell
  thirdRoot := degreeSevenStageSixFamilyInterval
    family.thirdLowerCell family.thirdUpperCell
  fourthRoot := degreeSevenStageSixFamilyInterval
    family.fourthLowerCell family.fourthUpperCell
  fifthRoot := degreeSevenStageSixFamilyInterval
    family.fifthLowerCell family.fifthUpperCell

/-- Integer numerator after multiplying a quintic value at `cell / 65536` by
`65536 ^ 5`. -/
def dyadicNumerator (family : DegreeSevenStageSixDyadicFamily)
    (a2 cell : ℤ) : ℤ :=
  a2 * 65536 ^ 5 +
    (3 * family.a3) * cell * 65536 ^ 4 +
    (6 * family.a4) * cell ^ 2 * 65536 ^ 3 +
    (10 * family.a5) * cell ^ 3 * 65536 ^ 2 +
    (15 * family.a6) * cell ^ 4 * 65536 +
    21 * cell ^ 5

/-- Fast integer form of all uniform signs, interval orders, and separations. -/
def ArithmeticValid (family : DegreeSevenStageSixDyadicFamily) : Prop :=
  family.a2Lower ≤ family.a2Upper ∧
    family.firstLowerCell < family.firstUpperCell ∧
    family.secondLowerCell < family.secondUpperCell ∧
    family.thirdLowerCell < family.thirdUpperCell ∧
    family.fourthLowerCell < family.fourthUpperCell ∧
    family.fifthLowerCell < family.fifthUpperCell ∧
    family.dyadicNumerator family.a2Upper family.firstLowerCell < 0 ∧
    0 < family.dyadicNumerator family.a2Lower family.firstUpperCell ∧
    0 < family.dyadicNumerator family.a2Lower family.secondLowerCell ∧
    family.dyadicNumerator family.a2Upper family.secondUpperCell < 0 ∧
    family.dyadicNumerator family.a2Upper family.thirdLowerCell < 0 ∧
    0 < family.dyadicNumerator family.a2Lower family.thirdUpperCell ∧
    0 < family.dyadicNumerator family.a2Lower family.fourthLowerCell ∧
    family.dyadicNumerator family.a2Upper family.fourthUpperCell < 0 ∧
    family.dyadicNumerator family.a2Upper family.fifthLowerCell < 0 ∧
    0 < family.dyadicNumerator family.a2Lower family.fifthUpperCell ∧
    family.firstUpperCell < family.secondLowerCell ∧
    family.secondUpperCell < family.thirdLowerCell ∧
    family.thirdUpperCell < family.fourthLowerCell ∧
    family.fourthUpperCell < family.fifthLowerCell

instance (family : DegreeSevenStageSixDyadicFamily) :
    Decidable family.ArithmeticValid := by
  unfold ArithmeticValid dyadicNumerator
  infer_instance

/-- Proof-facing validity of the expanded family. -/
def Valid (family : DegreeSevenStageSixDyadicFamily) : Prop :=
  family.toFamily.Valid

instance (family : DegreeSevenStageSixDyadicFamily) :
    Decidable family.Valid := by
  unfold Valid DegreeSevenStageSixFamily.Valid
  unfold DegreeSevenStageSixFamily.NegativePositive
  unfold DegreeSevenStageSixFamily.PositiveNegative
  unfold DegreeSevenStageSixFamily.eval
  unfold DegreeSevenStageSixFamily.derivativeCoefficients
  infer_instance

theorem rationalEval_eq_dyadicNumerator_div
    (family : DegreeSevenStageSixDyadicFamily)
    (a2 cell : ℤ) :
    integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / 65536) =
      (family.dyadicNumerator a2 cell : ℚ) / 65536 ^ 5 := by
  simp [integerPolynomialRationalEval, DensePolynomial.eval,
    dyadicNumerator]
  ring

private theorem dyadicEval_neg
    (family : DegreeSevenStageSixDyadicFamily)
    (a2 cell : ℤ) (h : family.dyadicNumerator a2 cell < 0) :
    integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / 65536) < 0 := by
  rw [rationalEval_eq_dyadicNumerator_div]
  apply div_neg_of_neg_of_pos
  · exact_mod_cast h
  · positivity

private theorem dyadicEval_pos
    (family : DegreeSevenStageSixDyadicFamily)
    (a2 cell : ℤ) (h : 0 < family.dyadicNumerator a2 cell) :
    0 < integerPolynomialRationalEval
        [a2, 3 * family.a3, 6 * family.a4, 10 * family.a5,
          15 * family.a6, 21]
        ((cell : ℚ) / 65536) := by
  rw [rationalEval_eq_dyadicNumerator_div]
  apply div_pos
  · exact_mod_cast h
  · positivity

private theorem dyadicCell_lt (x y : ℤ) (h : x < y) :
    (x : ℚ) / 65536 < (y : ℚ) / 65536 := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 65536)]
  exact_mod_cast h

/-- Integer arithmetic validity implies the general parametric certificate. -/
theorem valid_of_arithmeticValid
    (family : DegreeSevenStageSixDyadicFamily)
    (h : family.ArithmeticValid) : family.Valid := by
  rcases h with
    ⟨ha2, hfirstInterval, hsecondInterval, hthirdInterval, hfourthInterval,
      hfifthInterval, hfirstLower, hfirstUpper, hsecondLower, hsecondUpper,
      hthirdLower, hthirdUpper, hfourthLower, hfourthUpper, hfifthLower,
      hfifthUpper, h12, h23, h34, h45⟩
  unfold Valid DegreeSevenStageSixFamily.Valid
  refine ⟨ha2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dyadicCell_lt _ _ hfirstInterval
  · exact dyadicCell_lt _ _ hsecondInterval
  · exact dyadicCell_lt _ _ hthirdInterval
  · exact dyadicCell_lt _ _ hfourthInterval
  · exact dyadicCell_lt _ _ hfifthInterval
  · exact ⟨dyadicEval_neg family _ _ hfirstLower,
      dyadicEval_pos family _ _ hfirstUpper⟩
  · exact ⟨dyadicEval_pos family _ _ hsecondLower,
      dyadicEval_neg family _ _ hsecondUpper⟩
  · exact ⟨dyadicEval_neg family _ _ hthirdLower,
      dyadicEval_pos family _ _ hthirdUpper⟩
  · exact ⟨dyadicEval_pos family _ _ hfourthLower,
      dyadicEval_neg family _ _ hfourthUpper⟩
  · exact ⟨dyadicEval_neg family _ _ hfifthLower,
      dyadicEval_pos family _ _ hfifthUpper⟩
  · exact dyadicCell_lt _ _ h12
  · exact dyadicCell_lt _ _ h23
  · exact dyadicCell_lt _ _ h34
  · exact dyadicCell_lt _ _ h45

end DegreeSevenStageSixDyadicFamily

end

end TraceEuclidean
