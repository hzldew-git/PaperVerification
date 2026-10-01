import TraceEuclidean.DegreeSevenRolleStageSixBridge

/-!
# Exact six-root certificates for the final degree-seven Rolle stage

Once `a6`, ..., `a1` are fixed, the first derivative of the septic is a fixed
sextic.  This module records six rational isolating intervals with one
arbitrary positive common denominator.  Its integer arithmetic predicate is
designed for generated certificates and implies the ordinary proof-facing
root-interval certificate used by the final `a0` translation bound.
-/

namespace TraceEuclidean

noncomputable section

/-- A proof-facing final-stage entry with all coefficients above `a0` fixed. -/
structure DegreeSevenStageSevenEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
  fourthRoot : RationalRootInterval
  fifthRoot : RationalRootInterval
  sixthRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenEntry

def derivativeCoefficients (entry : DegreeSevenStageSevenEntry) : List ℤ :=
  [entry.a1, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4,
    5 * entry.a5, 6 * entry.a6, 7]

def baseCoefficients (entry : DegreeSevenStageSevenEntry) : List ℤ :=
  [0, entry.a1, entry.a2, entry.a3, entry.a4, entry.a5, entry.a6, 1]

def rootIntervals (entry : DegreeSevenStageSevenEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot,
    entry.fourthRoot, entry.fifthRoot, entry.sixthRoot]

def Valid (entry : DegreeSevenStageSevenEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 6
    entry.derivativeCoefficients entry.rootIntervals

instance (entry : DegreeSevenStageSevenEntry) : Decidable entry.Valid := by
  unfold Valid
  infer_instance

def leftEndpoint (entry : DegreeSevenStageSevenEntry) : ℚ :=
  (-(entry.a6 : ℚ) - 38) / 7

def rightEndpoint (entry : DegreeSevenStageSevenEntry) : ℚ :=
  (-(entry.a6 : ℚ) + 38) / 7

def a0Candidates (entry : DegreeSevenStageSevenEntry) : Finset ℤ :=
  septicTranslationCandidates entry.baseCoefficients
    entry.leftEndpoint entry.rightEndpoint entry.firstRoot entry.secondRoot
    entry.thirdRoot entry.fourthRoot entry.fifthRoot entry.sixthRoot

end DegreeSevenStageSevenEntry

/-- Integer storage for a variable-precision final-stage certificate. -/
structure DegreeSevenStageSevenScaledEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
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
  sixthLower : ℤ
  sixthUpper : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageSevenScaledEntry

def interval (entry : DegreeSevenStageSevenScaledEntry)
    (lower upper : ℤ) : RationalRootInterval where
  lower := (lower : ℚ) / entry.denominator
  upper := (upper : ℚ) / entry.denominator

def toEntry (entry : DegreeSevenStageSevenScaledEntry) :
    DegreeSevenStageSevenEntry where
  a6 := entry.a6
  a5 := entry.a5
  a4 := entry.a4
  a3 := entry.a3
  a2 := entry.a2
  a1 := entry.a1
  firstRoot := entry.interval entry.firstLower entry.firstUpper
  secondRoot := entry.interval entry.secondLower entry.secondUpper
  thirdRoot := entry.interval entry.thirdLower entry.thirdUpper
  fourthRoot := entry.interval entry.fourthLower entry.fourthUpper
  fifthRoot := entry.interval entry.fifthLower entry.fifthUpper
  sixthRoot := entry.interval entry.sixthLower entry.sixthUpper

/-- Numerator of the sextic value after clearing `denominator ^ 6`. -/
def scaledNumerator (entry : DegreeSevenStageSevenScaledEntry)
    (cell : ℤ) : ℤ :=
  entry.a1 * entry.denominator ^ 6 +
    (2 * entry.a2) * cell * entry.denominator ^ 5 +
    (3 * entry.a3) * cell ^ 2 * entry.denominator ^ 4 +
    (4 * entry.a4) * cell ^ 3 * entry.denominator ^ 3 +
    (5 * entry.a5) * cell ^ 4 * entry.denominator ^ 2 +
    (6 * entry.a6) * cell ^ 5 * entry.denominator +
    7 * cell ^ 6

/-- Pure integer form of interval validity and strict root separation. -/
def ArithmeticValid (entry : DegreeSevenStageSevenScaledEntry) : Prop :=
  0 < entry.denominator ∧
    entry.firstLower < entry.firstUpper ∧
    entry.secondLower < entry.secondUpper ∧
    entry.thirdLower < entry.thirdUpper ∧
    entry.fourthLower < entry.fourthUpper ∧
    entry.fifthLower < entry.fifthUpper ∧
    entry.sixthLower < entry.sixthUpper ∧
    entry.scaledNumerator entry.firstLower *
      entry.scaledNumerator entry.firstUpper < 0 ∧
    entry.scaledNumerator entry.secondLower *
      entry.scaledNumerator entry.secondUpper < 0 ∧
    entry.scaledNumerator entry.thirdLower *
      entry.scaledNumerator entry.thirdUpper < 0 ∧
    entry.scaledNumerator entry.fourthLower *
      entry.scaledNumerator entry.fourthUpper < 0 ∧
    entry.scaledNumerator entry.fifthLower *
      entry.scaledNumerator entry.fifthUpper < 0 ∧
    entry.scaledNumerator entry.sixthLower *
      entry.scaledNumerator entry.sixthUpper < 0 ∧
    entry.firstUpper < entry.secondLower ∧
    entry.secondUpper < entry.thirdLower ∧
    entry.thirdUpper < entry.fourthLower ∧
    entry.fourthUpper < entry.fifthLower ∧
    entry.fifthUpper < entry.sixthLower

instance (entry : DegreeSevenStageSevenScaledEntry) :
    Decidable entry.ArithmeticValid := by
  unfold ArithmeticValid scaledNumerator
  infer_instance

theorem rationalEval_eq_scaledNumerator_div
    (entry : DegreeSevenStageSevenScaledEntry)
    (cell : ℤ) (hdenominator : entry.denominator ≠ 0) :
    integerPolynomialRationalEval
        entry.toEntry.derivativeCoefficients
        ((cell : ℚ) / entry.denominator) =
      (entry.scaledNumerator cell : ℚ) / entry.denominator ^ 6 := by
  simp [DegreeSevenStageSevenEntry.derivativeCoefficients, toEntry,
    integerPolynomialRationalEval, DensePolynomial.eval,
    scaledNumerator]
  field_simp [hdenominator]
  ring

private theorem scaledProduct_neg
    (entry : DegreeSevenStageSevenScaledEntry)
    (lower upper : ℤ) (hdenominator : 0 < entry.denominator)
    (hproduct : entry.scaledNumerator lower *
      entry.scaledNumerator upper < 0) :
    integerPolynomialRationalEval entry.toEntry.derivativeCoefficients
        ((lower : ℚ) / entry.denominator) *
      integerPolynomialRationalEval entry.toEntry.derivativeCoefficients
        ((upper : ℚ) / entry.denominator) < 0 := by
  rw [entry.rationalEval_eq_scaledNumerator_div lower
      (ne_of_gt hdenominator),
    entry.rationalEval_eq_scaledNumerator_div upper
      (ne_of_gt hdenominator)]
  have hnumerator :
      (entry.scaledNumerator lower : ℚ) *
        entry.scaledNumerator upper < 0 := by
    exact_mod_cast hproduct
  have hpower : 0 < (entry.denominator : ℚ) ^ 6 := by
    positivity
  rw [div_mul_div_comm]
  exact div_neg_of_neg_of_pos hnumerator (mul_pos hpower hpower)

private theorem scaledCell_lt
    (entry : DegreeSevenStageSevenScaledEntry)
    (x y : ℤ) (hdenominator : 0 < entry.denominator) (h : x < y) :
    (x : ℚ) / entry.denominator < (y : ℚ) / entry.denominator := by
  rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hdenominator)]
  exact_mod_cast h

/-- Integer arithmetic validity gives a complete six-root certificate. -/
theorem valid_of_arithmeticValid
    (entry : DegreeSevenStageSevenScaledEntry)
    (h : entry.ArithmeticValid) : entry.toEntry.Valid := by
  rcases h with
    ⟨hdenominator, hfirstInterval, hsecondInterval, hthirdInterval,
      hfourthInterval, hfifthInterval, hsixthInterval,
      hfirstSign, hsecondSign, hthirdSign, hfourthSign, hfifthSign,
      hsixthSign, h12, h23, h34, h45, h56⟩
  unfold DegreeSevenStageSevenEntry.Valid
  unfold GeneralRationalRootIntervalCertificate.Valid
  refine ⟨by norm_num, by norm_num
      [DegreeSevenStageSevenEntry.derivativeCoefficients, toEntry],
    by norm_num [DegreeSevenStageSevenEntry.derivativeCoefficients, toEntry],
    by norm_num [DegreeSevenStageSevenEntry.rootIntervals, toEntry], ?_, ?_⟩
  · simp only [DegreeSevenStageSevenEntry.rootIntervals, toEntry,
      List.forall_cons]
    exact ⟨
      ⟨scaledCell_lt entry _ _ hdenominator hfirstInterval,
        scaledProduct_neg entry _ _ hdenominator hfirstSign⟩,
      ⟨scaledCell_lt entry _ _ hdenominator hsecondInterval,
        scaledProduct_neg entry _ _ hdenominator hsecondSign⟩,
      ⟨scaledCell_lt entry _ _ hdenominator hthirdInterval,
        scaledProduct_neg entry _ _ hdenominator hthirdSign⟩,
      ⟨scaledCell_lt entry _ _ hdenominator hfourthInterval,
        scaledProduct_neg entry _ _ hdenominator hfourthSign⟩,
      ⟨scaledCell_lt entry _ _ hdenominator hfifthInterval,
        scaledProduct_neg entry _ _ hdenominator hfifthSign⟩,
      ⟨scaledCell_lt entry _ _ hdenominator hsixthInterval,
        scaledProduct_neg entry _ _ hdenominator hsixthSign⟩, trivial⟩
  · simp only [DegreeSevenStageSevenEntry.rootIntervals, toEntry,
      List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    simp
    have h12q := scaledCell_lt entry _ _ hdenominator h12
    have h23q := scaledCell_lt entry _ _ hdenominator h23
    have h34q := scaledCell_lt entry _ _ hdenominator h34
    have h45q := scaledCell_lt entry _ _ hdenominator h45
    have h56q := scaledCell_lt entry _ _ hdenominator h56
    have h2q := scaledCell_lt entry _ _ hdenominator hsecondInterval
    have h3q := scaledCell_lt entry _ _ hdenominator hthirdInterval
    have h4q := scaledCell_lt entry _ _ hdenominator hfourthInterval
    have h5q := scaledCell_lt entry _ _ hdenominator hfifthInterval
    have h13 := h12q.trans (h2q.trans h23q)
    have h24 := h23q.trans (h3q.trans h34q)
    have h35 := h34q.trans (h4q.trans h45q)
    have h46 := h45q.trans (h5q.trans h56q)
    have h14 := h13.trans (h3q.trans h34q)
    have h25 := h24.trans (h4q.trans h45q)
    have h36 := h35.trans (h5q.trans h56q)
    have h15 := h14.trans (h4q.trans h45q)
    have h26 := h25.trans (h5q.trans h56q)
    have h16 := h15.trans (h5q.trans h56q)
    exact ⟨⟨h12q, h13, h14, h15, h16⟩,
      ⟨h23q, h24, h25, h26⟩,
      ⟨h34q, h35, h36⟩,
      ⟨h45q, h46⟩, h56q⟩

end DegreeSevenStageSevenScaledEntry

end

end TraceEuclidean
