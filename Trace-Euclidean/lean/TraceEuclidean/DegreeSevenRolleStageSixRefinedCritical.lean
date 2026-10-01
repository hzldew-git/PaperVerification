import TraceEuclidean.DegreeSevenRolleStageSixStrongCoverage
import TraceEuclidean.DegreeSevenRolleStageFiveCompact
import TraceEuclidean.ScaledIntegerPolynomialInterval

/-!
# Cleared-denominator refined critical-point certificates

An exceptional Stage Six boundary sometimes needs root intervals narrower than
the Stage Five dyadic cells.  All eight refined endpoints are stored with one
positive integer denominator.  Root isolation and the critical-value sign are
then checked entirely in `ℤ`; the theorems below bridge those checks back to the
general rational certificates used by the Rolle argument.
-/

namespace TraceEuclidean

noncomputable section

/-- Four ordered rational intervals with one common positive denominator. -/
structure DegreeSevenStageFiveScaledRoots where
  denominator : ℤ
  firstLower : ℤ
  firstUpper : ℤ
  secondLower : ℤ
  secondUpper : ℤ
  thirdLower : ℤ
  thirdUpper : ℤ
  fourthLower : ℤ
  fourthUpper : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveScaledRoots

def interval (roots : DegreeSevenStageFiveScaledRoots)
    (lower upper : ℤ) : RationalRootInterval where
  lower := (lower : ℚ) / roots.denominator
  upper := (upper : ℚ) / roots.denominator

def toEntry (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    DegreeSevenStageFiveEntry where
  a6 := parent.a6
  a5 := parent.a5
  a4 := parent.a4
  a3 := parent.a3
  firstRoot := roots.interval roots.firstLower roots.firstUpper
  secondRoot := roots.interval roots.secondLower roots.secondUpper
  thirdRoot := roots.interval roots.thirdLower roots.thirdUpper
  fourthRoot := roots.interval roots.fourthLower roots.fourthUpper

/-- Numerator of the quartic derivative value after clearing
`denominator ^ 4`. -/
def scaledNumerator (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry) (cell : ℤ) : ℤ :=
  parent.a3 * roots.denominator ^ 4 +
    (4 * parent.a4) * cell * roots.denominator ^ 3 +
    (10 * parent.a5) * cell ^ 2 * roots.denominator ^ 2 +
    (20 * parent.a6) * cell ^ 3 * roots.denominator +
    35 * cell ^ 4

/-- Purely integral validity check for the four refined intervals. -/
def ArithmeticValid (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  0 < roots.denominator ∧
    roots.firstLower < roots.firstUpper ∧
    roots.scaledNumerator parent roots.firstLower *
      roots.scaledNumerator parent roots.firstUpper < 0 ∧
    roots.secondLower < roots.secondUpper ∧
    roots.scaledNumerator parent roots.secondLower *
      roots.scaledNumerator parent roots.secondUpper < 0 ∧
    roots.thirdLower < roots.thirdUpper ∧
    roots.scaledNumerator parent roots.thirdLower *
      roots.scaledNumerator parent roots.thirdUpper < 0 ∧
    roots.fourthLower < roots.fourthUpper ∧
    roots.scaledNumerator parent roots.fourthLower *
      roots.scaledNumerator parent roots.fourthUpper < 0 ∧
    roots.firstUpper < roots.secondLower ∧
    roots.secondUpper < roots.thirdLower ∧
    roots.thirdUpper < roots.fourthLower

instance (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (roots.ArithmeticValid parent) := by
  unfold ArithmeticValid
  infer_instance

theorem rationalEval_eq_scaledNumerator_div
    (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry) (cell : ℤ)
    (hdenominator : roots.denominator ≠ 0) :
    integerPolynomialRationalEval
        [parent.a3, 4 * parent.a4, 10 * parent.a5,
          20 * parent.a6, 35]
        ((cell : ℚ) / roots.denominator) =
      (roots.scaledNumerator parent cell : ℚ) /
        roots.denominator ^ 4 := by
  simp [integerPolynomialRationalEval, DensePolynomial.eval,
    scaledNumerator]
  field_simp [hdenominator]
  ring

private theorem scaledProduct_neg (denominator x y : ℤ)
    (hdenominator : 0 < denominator) (h : x * y < 0) :
    ((x : ℚ) / denominator ^ 4) *
        ((y : ℚ) / denominator ^ 4) < 0 := by
  have hxy : (((x * y : ℤ) : ℚ)) < 0 := by exact_mod_cast h
  have hpow : (0 : ℚ) < (denominator : ℚ) ^ 4 := by
    positivity
  calc
    ((x : ℚ) / denominator ^ 4) *
        ((y : ℚ) / denominator ^ 4) =
      (((x * y : ℤ) : ℚ)) /
        ((denominator : ℚ) ^ 4 * denominator ^ 4) := by
          push_cast
          ring
    _ < 0 := div_neg_of_neg_of_pos hxy (mul_pos hpow hpow)

private theorem scaledInterval_valid
    (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (lower upper : ℤ) (hdenominator : 0 < roots.denominator)
    (hordered : lower < upper)
    (hsign : roots.scaledNumerator parent lower *
      roots.scaledNumerator parent upper < 0) :
    let interval := roots.interval lower upper
    interval.lower < interval.upper ∧
      integerPolynomialRationalEval
          [parent.a3, 4 * parent.a4, 10 * parent.a5,
            20 * parent.a6, 35] interval.lower *
        integerPolynomialRationalEval
          [parent.a3, 4 * parent.a4, 10 * parent.a5,
            20 * parent.a6, 35] interval.upper < 0 := by
  dsimp [interval]
  constructor
  · rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hdenominator)]
    exact_mod_cast hordered
  · rw [rationalEval_eq_scaledNumerator_div _ _ _
      (ne_of_gt hdenominator),
      rationalEval_eq_scaledNumerator_div _ _ _
        (ne_of_gt hdenominator)]
    exact scaledProduct_neg roots.denominator _ _ hdenominator hsign

private theorem scaledUpper_lt_lower
    (roots : DegreeSevenStageFiveScaledRoots)
    (leftUpper rightLower : ℤ) (hdenominator : 0 < roots.denominator)
    (h : leftUpper < rightLower) :
    (roots.interval 0 leftUpper).upper <
      (roots.interval rightLower 0).lower := by
  dsimp [interval]
  rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hdenominator)]
  exact_mod_cast h

/-- The integral scaled checks imply the general rational root certificate. -/
theorem valid_of_arithmeticValid
    (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : roots.ArithmeticValid parent) : (roots.toEntry parent).Valid := by
  rcases h with
    ⟨hdenominator, hfirstOrder, hfirst, hsecondOrder, hsecond,
      hthirdOrder, hthird, hfourthOrder, hfourth, h12, h23, h34⟩
  unfold DegreeSevenStageFiveEntry.Valid
  unfold GeneralRationalRootIntervalCertificate.Valid
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [toEntry, DegreeSevenStageFiveEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageFiveEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageFiveEntry.rootIntervals]
  · simp only [toEntry, DegreeSevenStageFiveEntry.rootIntervals,
      List.forall_cons]
    exact ⟨scaledInterval_valid roots parent _ _ hdenominator
        hfirstOrder hfirst,
      scaledInterval_valid roots parent _ _ hdenominator
        hsecondOrder hsecond,
      scaledInterval_valid roots parent _ _ hdenominator
        hthirdOrder hthird,
      scaledInterval_valid roots parent _ _ hdenominator
        hfourthOrder hfourth, trivial⟩
  · simp only [toEntry, DegreeSevenStageFiveEntry.rootIntervals,
      List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    simp only [interval]
    repeat' apply And.intro
    all_goals
      first
      | simp
      | (rw [div_lt_div_iff_of_pos_right
          (by exact_mod_cast hdenominator : (0 : ℚ) < roots.denominator)]
         exact_mod_cast (by omega))

def lower (roots : DegreeSevenStageFiveScaledRoots) :
    DegreeSevenStageSixCriticalPoint → ℤ
  | .first => roots.firstLower
  | .second => roots.secondLower
  | .third => roots.thirdLower
  | .fourth => roots.fourthLower

def upper (roots : DegreeSevenStageFiveScaledRoots) :
    DegreeSevenStageSixCriticalPoint → ℤ
  | .first => roots.firstUpper
  | .second => roots.secondUpper
  | .third => roots.thirdUpper
  | .fourth => roots.fourthUpper

theorem lower_lt_upper_of_arithmeticValid
    (roots : DegreeSevenStageFiveScaledRoots)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (point : DegreeSevenStageSixCriticalPoint)
    (h : roots.ArithmeticValid parent) : roots.lower point < roots.upper point := by
  rcases h with ⟨_, hfirst, _, hsecond, _, hthird, _, hfourth, _⟩
  cases point <;> assumption

end DegreeSevenStageFiveScaledRoots

/-- Refined critical-sign rejection checked with a common integer
denominator. -/
structure DegreeSevenStageSixRefinedCriticalSign where
  a2 : ℤ
  point : DegreeSevenStageSixCriticalPoint
  roots : DegreeSevenStageFiveScaledRoots
deriving DecidableEq, Repr

namespace DegreeSevenStageSixRefinedCriticalSign

def toWitness (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    DegreeSevenStageSixCriticalSignWitness :=
  ⟨critical.roots.toEntry parent, critical.a2, critical.point⟩

def scaledCriticalRange
    (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) : ℤ × ℤ :=
  scaledIntegerPolynomialIntervalEval critical.roots.denominator
    (critical.roots.lower critical.point)
    (critical.roots.upper critical.point)
    (critical.toWitness parent).coefficients

def ArithmeticValid
    (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  critical.roots.ArithmeticValid parent ∧
    match critical.point with
    | .first => (critical.scaledCriticalRange parent).2 < 0
    | .second => 0 < (critical.scaledCriticalRange parent).1
    | .third => (critical.scaledCriticalRange parent).2 < 0
    | .fourth => 0 < (critical.scaledCriticalRange parent).1

def Valid (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) : Prop :=
  (critical.toWitness parent).Valid

instance (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (critical.ArithmeticValid parent) := by
  unfold ArithmeticValid
  cases critical.point <;> infer_instance

instance (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    Decidable (critical.Valid parent) := by
  unfold Valid
  infer_instance

private theorem criticalValueRange_eq_scaled
    (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (hroots : critical.roots.ArithmeticValid parent) :
    (critical.toWitness parent).criticalValueRange.lo =
        ((critical.scaledCriticalRange parent).1 : ℚ) /
          critical.roots.denominator ^ 6 ∧
      (critical.toWitness parent).criticalValueRange.hi =
        ((critical.scaledCriticalRange parent).2 : ℚ) /
          critical.roots.denominator ^ 6 := by
  have hdenominator : 0 < critical.roots.denominator := hroots.1
  have hordered := critical.roots.lower_lt_upper_of_arithmeticValid
    parent critical.point hroots
  have hcorrect := scaledIntegerPolynomialIntervalEval_correct
    (critical.toWitness parent).coefficients critical.roots.denominator
    (critical.roots.lower critical.point)
    (critical.roots.upper critical.point) hdenominator hordered.le
  have horderedRat :
      ((critical.roots.lower critical.point : ℤ) : ℚ) /
          critical.roots.denominator ≤
        ((critical.roots.upper critical.point : ℤ) : ℚ) /
          critical.roots.denominator := by
    rw [div_le_div_iff_of_pos_right
      (by exact_mod_cast hdenominator : (0 : ℚ) < critical.roots.denominator)]
    exact_mod_cast hordered.le
  dsimp only at hcorrect
  let input : LeanCert.Core.IntervalRat :=
    ⟨(critical.roots.lower critical.point : ℚ) /
        critical.roots.denominator,
      (critical.roots.upper critical.point : ℚ) /
        critical.roots.denominator, horderedRat⟩
  have hinterval :
      (critical.point.interval (critical.toWitness parent).parent).toIntervalRat =
        input := by
    cases hpoint : critical.point
    all_goals
      simp only [hpoint, DegreeSevenStageFiveScaledRoots.lower,
        DegreeSevenStageFiveScaledRoots.upper] at horderedRat ⊢
      simp [input, toWitness,
        DegreeSevenStageSixCriticalPoint.interval,
        DegreeSevenStageFiveScaledRoots.toEntry,
        DegreeSevenStageFiveScaledRoots.interval,
        DegreeSevenStageFiveScaledRoots.lower,
        DegreeSevenStageFiveScaledRoots.upper,
        RationalRootInterval.toIntervalRat, hpoint, horderedRat]
  unfold DegreeSevenStageSixCriticalSignWitness.criticalValueRange
  unfold integerPolynomialRootIntervalEval
  rw [show (critical.toWitness parent).point = critical.point by rfl,
    hinterval]
  simpa [input, scaledCriticalRange, toWitness,
    DegreeSevenStageSixCriticalSignWitness.coefficients,
    DegreeSevenStageFiveScaledRoots.toEntry,
    integerPolynomialIntervalEval] using hcorrect

theorem valid_of_arithmeticValid
    (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry)
    (h : critical.ArithmeticValid parent) : critical.Valid parent := by
  rcases h with ⟨hroots, hsign⟩
  unfold Valid DegreeSevenStageSixCriticalSignWitness.Valid
  refine ⟨critical.roots.valid_of_arithmeticValid parent hroots, ?_⟩
  have hrange := criticalValueRange_eq_scaled critical parent hroots
  have hdenominator : (0 : ℚ) < critical.roots.denominator ^ 6 := by
    exact pow_pos (by exact_mod_cast hroots.1) _
  change
    match critical.point with
    | .first => (critical.toWitness parent).criticalValueRange.hi < 0
    | .second => 0 < (critical.toWitness parent).criticalValueRange.lo
    | .third => (critical.toWitness parent).criticalValueRange.hi < 0
    | .fourth => 0 < (critical.toWitness parent).criticalValueRange.lo
  cases hpoint : critical.point
  · simp only [hpoint] at hsign ⊢
    rw [hrange.2]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hsign) hdenominator
  · simp only [hpoint] at hsign ⊢
    rw [hrange.1]
    exact div_pos (by exact_mod_cast hsign) hdenominator
  · simp only [hpoint] at hsign ⊢
    rw [hrange.2]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hsign) hdenominator
  · simp only [hpoint] at hsign ⊢
    rw [hrange.1]
    exact div_pos (by exact_mod_cast hsign) hdenominator

theorem sameTop (critical : DegreeSevenStageSixRefinedCriticalSign)
    (parent : DegreeSevenStageFiveDyadicEntry) :
    (critical.toWitness parent).SameTop parent := by
  unfold DegreeSevenStageSixCriticalSignWitness.SameTop
  simp [toWitness, DegreeSevenStageFiveScaledRoots.toEntry]

end DegreeSevenStageSixRefinedCriticalSign

end

end TraceEuclidean
