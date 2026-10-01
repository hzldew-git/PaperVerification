import TraceEuclidean.DegreeSevenRolleStageFiveBridge

/-!
# Compact certificates for the fifth degree-seven Rolle stage

All simple quartics in the current fourth-stage frontier admit four strictly
separated sign-changing intervals of width `2 / 4096`.  A certificate can
therefore store one integer cell coordinate per root instead of eight
arbitrary rational endpoints.  The definitions below retain the same
proof-facing interface as the general rational certificate.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- The common denominator used by the compact degree-seven root cells. -/
def degreeSevenStageFiveDyadicDenominator : ℕ := 4096

/-- A width-two dyadic cell.  The extra unit ensures that a rational root on
a grid boundary is still strictly bracketed by the two endpoints. -/
def degreeSevenStageFiveDyadicInterval
    (cell : ℤ) : RationalRootInterval where
  lower := (cell : ℚ) / degreeSevenStageFiveDyadicDenominator
  upper := ((cell + 2 : ℤ) : ℚ) /
    degreeSevenStageFiveDyadicDenominator

/-- The compact representation of one simple quartic row. -/
structure DegreeSevenStageFiveDyadicEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  firstCell : ℤ
  secondCell : ℤ
  thirdCell : ℤ
  fourthCell : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveDyadicEntry

/-- Expand the compact row into the general proof-facing certificate. -/
def toEntry (entry : DegreeSevenStageFiveDyadicEntry) :
    DegreeSevenStageFiveEntry where
  a6 := entry.a6
  a5 := entry.a5
  a4 := entry.a4
  a3 := entry.a3
  firstRoot := degreeSevenStageFiveDyadicInterval entry.firstCell
  secondRoot := degreeSevenStageFiveDyadicInterval entry.secondCell
  thirdRoot := degreeSevenStageFiveDyadicInterval entry.thirdCell
  fourthRoot := degreeSevenStageFiveDyadicInterval entry.fourthCell

/-- Kernel-checkable validity of a compact row. -/
def Valid (entry : DegreeSevenStageFiveDyadicEntry) : Prop :=
  entry.toEntry.Valid

instance (entry : DegreeSevenStageFiveDyadicEntry) :
    Decidable entry.Valid := by
  unfold Valid DegreeSevenStageFiveEntry.Valid
  infer_instance

/-- The integer numerator obtained after multiplying the quartic value at
`cell / 4096` by `4096 ^ 4`.  Keeping generated checks in `ℤ` avoids repeated
normalization of large rational denominators. -/
def dyadicNumerator (entry : DegreeSevenStageFiveDyadicEntry)
    (cell : ℤ) : ℤ :=
  entry.a3 * 4096 ^ 4 +
    (4 * entry.a4) * cell * 4096 ^ 3 +
    (10 * entry.a5) * cell ^ 2 * 4096 ^ 2 +
    (20 * entry.a6) * cell ^ 3 * 4096 +
    35 * cell ^ 4

/-- A computationally efficient integer form of the four sign changes and
the strict ordering of their dyadic cells. -/
def ArithmeticValid (entry : DegreeSevenStageFiveDyadicEntry) : Prop :=
  entry.dyadicNumerator entry.firstCell *
      entry.dyadicNumerator (entry.firstCell + 2) < 0 ∧
    entry.dyadicNumerator entry.secondCell *
      entry.dyadicNumerator (entry.secondCell + 2) < 0 ∧
    entry.dyadicNumerator entry.thirdCell *
      entry.dyadicNumerator (entry.thirdCell + 2) < 0 ∧
    entry.dyadicNumerator entry.fourthCell *
      entry.dyadicNumerator (entry.fourthCell + 2) < 0 ∧
    entry.firstCell + 2 < entry.secondCell ∧
    entry.secondCell + 2 < entry.thirdCell ∧
    entry.thirdCell + 2 < entry.fourthCell

instance (entry : DegreeSevenStageFiveDyadicEntry) :
    Decidable entry.ArithmeticValid := by
  unfold ArithmeticValid
  infer_instance

theorem rationalEval_eq_dyadicNumerator_div
    (entry : DegreeSevenStageFiveDyadicEntry) (cell : ℤ) :
    integerPolynomialRationalEval
        [entry.a3, 4 * entry.a4, 10 * entry.a5,
          20 * entry.a6, 35]
        ((cell : ℚ) / 4096) =
      (entry.dyadicNumerator cell : ℚ) / 4096 ^ 4 := by
  simp [integerPolynomialRationalEval, DensePolynomial.eval,
    dyadicNumerator]
  ring

private theorem dyadicProduct_neg (x y : ℤ) (h : x * y < 0) :
    ((x : ℚ) / 4096 ^ 4) * ((y : ℚ) / 4096 ^ 4) < 0 := by
  have hxy : (((x * y : ℤ) : ℚ)) < 0 := by
    exact_mod_cast h
  calc
    ((x : ℚ) / 4096 ^ 4) * ((y : ℚ) / 4096 ^ 4) =
        (((x * y : ℤ) : ℚ)) /
          ((4096 : ℚ) ^ 4 * 4096 ^ 4) := by
      push_cast
      ring
    _ < 0 := div_neg_of_neg_of_pos hxy (by positivity)

private theorem dyadicInterval_valid
    (entry : DegreeSevenStageFiveDyadicEntry) (cell : ℤ)
    (h : entry.dyadicNumerator cell *
      entry.dyadicNumerator (cell + 2) < 0) :
    let interval := degreeSevenStageFiveDyadicInterval cell
    interval.lower < interval.upper ∧
      integerPolynomialRationalEval
          [entry.a3, 4 * entry.a4, 10 * entry.a5,
            20 * entry.a6, 35] interval.lower *
        integerPolynomialRationalEval
          [entry.a3, 4 * entry.a4, 10 * entry.a5,
            20 * entry.a6, 35] interval.upper < 0 := by
  dsimp [degreeSevenStageFiveDyadicInterval,
    degreeSevenStageFiveDyadicDenominator]
  constructor
  · rw [div_lt_div_iff_of_pos_right
      (by norm_num : (0 : ℚ) < 4096)]
    norm_num
  · rw [rationalEval_eq_dyadicNumerator_div,
      rationalEval_eq_dyadicNumerator_div]
    exact dyadicProduct_neg _ _ h

private theorem dyadicUpper_lt_lower (x y : ℤ) (h : x + 2 < y) :
    (degreeSevenStageFiveDyadicInterval x).upper <
      (degreeSevenStageFiveDyadicInterval y).lower := by
  dsimp [degreeSevenStageFiveDyadicInterval,
    degreeSevenStageFiveDyadicDenominator]
  rw [div_lt_div_iff_of_pos_right
    (by norm_num : (0 : ℚ) < 4096)]
  exact_mod_cast h

/-- Integer dyadic checks imply the original general rational certificate,
so the faster generated proof has exactly the same proof-facing conclusion. -/
theorem valid_of_arithmeticValid
    (entry : DegreeSevenStageFiveDyadicEntry)
    (h : entry.ArithmeticValid) : entry.Valid := by
  rcases h with
    ⟨hfirst, hsecond, hthird, hfourth, h12, h23, h34⟩
  unfold Valid DegreeSevenStageFiveEntry.Valid
  unfold GeneralRationalRootIntervalCertificate.Valid
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [toEntry, DegreeSevenStageFiveEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageFiveEntry.derivativeCoefficients]
  · norm_num [toEntry, DegreeSevenStageFiveEntry.rootIntervals]
  · simp only [toEntry, DegreeSevenStageFiveEntry.rootIntervals,
      List.forall_cons]
    exact ⟨dyadicInterval_valid entry entry.firstCell hfirst,
      dyadicInterval_valid entry entry.secondCell hsecond,
      dyadicInterval_valid entry entry.thirdCell hthird,
      dyadicInterval_valid entry entry.fourthCell hfourth, trivial⟩
  · simp only [toEntry, DegreeSevenStageFiveEntry.rootIntervals,
      List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    simp
    repeat' apply And.intro
    all_goals apply dyadicUpper_lt_lower
    all_goals omega

/-- The exact `a2` candidates attached to a compact row. -/
def a2Candidates (entry : DegreeSevenStageFiveDyadicEntry) : Finset ℤ :=
  entry.toEntry.a2Candidates

end DegreeSevenStageFiveDyadicEntry

/-- The generic fifth-stage bridge applies directly to every valid compact
row. -/
theorem degreeSeven_minimumHunterCandidate_a2_mem_of_valid_dyadic
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageFiveDyadicEntry)
    (hvalid : entry.Valid)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3) :
    f.coeff 2 ∈ entry.a2Candidates := by
  exact degreeSeven_minimumHunterCandidate_a2_mem_of_valid
    h entry.toEntry hvalid ha6 ha5 ha4 ha3

/-- A compact witness for a discarded quartic with a common integral root
of the quartic and its derivative. -/
structure DegreeSevenStageFiveMultipleRootWitness where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  root : ℤ
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveMultipleRootWitness

def coefficients
    (witness : DegreeSevenStageFiveMultipleRootWitness) : List ℤ :=
  [witness.a3, 4 * witness.a4, 10 * witness.a5,
    20 * witness.a6, 35]

def derivativeCoefficients
    (witness : DegreeSevenStageFiveMultipleRootWitness) : List ℤ :=
  [4 * witness.a4, 20 * witness.a5, 60 * witness.a6, 140, 0]

def Valid (witness : DegreeSevenStageFiveMultipleRootWitness) : Prop :=
  integerPolynomialRationalEval witness.coefficients witness.root = 0 ∧
    integerPolynomialRationalEval witness.derivativeCoefficients
      witness.root = 0

instance (witness : DegreeSevenStageFiveMultipleRootWitness) :
    Decidable witness.Valid := by
  unfold Valid
  infer_instance

end DegreeSevenStageFiveMultipleRootWitness

private theorem degreeSeven_integerPolynomial_eval_ratCast
    (coefficients : List ℤ) (x : ℚ) :
    (integerPolynomialReal coefficients).eval (x : ℝ) =
      (integerPolynomialRationalEval coefficients x : ℝ) := by
  rw [integerPolynomialReal, ← DensePolynomial.toPolynomial_map]
  rw [DensePolynomial.eval_toPolynomial]
  change DensePolynomial.eval
    (coefficients.map (Int.castRingHom ℝ)) (x : ℝ) = _
  rw [show coefficients.map (Int.castRingHom ℝ) =
      (coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ) by simp]
  change DensePolynomial.eval
      ((coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ)) (algebraMap ℚ ℝ x) =
    algebraMap ℚ ℝ (integerPolynomialRationalEval coefficients x)
  unfold integerPolynomialRationalEval
  exact DensePolynomial.eval_map (algebraMap ℚ ℝ)
    (coefficients.map (Int.castRingHom ℚ)) x

/-- A valid common-root witness excludes the corresponding quartic from a
separable Hunter derivative stage. -/
theorem degreeSevenStageFiveMultipleRootWitness_not_separable
    (witness : DegreeSevenStageFiveMultipleRootWitness)
    (hvalid : witness.Valid) :
    ¬(integerPolynomialReal witness.coefficients).Separable := by
  apply degreeSeven_not_separable_of_common_real_root
      (x := (witness.root : ℝ))
  · rw [show (witness.root : ℝ) = ((witness.root : ℚ) : ℝ) by simp,
      degreeSeven_integerPolynomial_eval_ratCast]
    exact_mod_cast hvalid.1
  · rw [integerPolynomialReal_derivative]
    have hcoefficients :
        DensePolynomial.derivative witness.coefficients =
          witness.derivativeCoefficients := by
      simp [DegreeSevenStageFiveMultipleRootWitness.coefficients,
        DegreeSevenStageFiveMultipleRootWitness.derivativeCoefficients,
        DensePolynomial.derivative, DensePolynomial.add]
      constructor <;> ring
    rw [hcoefficients,
      show (witness.root : ℝ) = ((witness.root : ℚ) : ℝ) by simp,
      degreeSeven_integerPolynomial_eval_ratCast]
    exact_mod_cast hvalid.2

/-- The three critical points of the quartic at the fifth Rolle stage. -/
inductive DegreeSevenStageFiveCriticalPoint where
  | first
  | second
  | third
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveCriticalPoint

/-- Index of the critical point in the increasing list of derivative roots. -/
def index : DegreeSevenStageFiveCriticalPoint → Fin 3
  | first => ⟨0, by norm_num⟩
  | second => ⟨1, by norm_num⟩
  | third => ⟨2, by norm_num⟩

/-- Certified cubic-root interval containing the selected critical point. -/
def interval (point : DegreeSevenStageFiveCriticalPoint)
    (parent : DegreeSevenStageFourEntry) : RationalRootInterval :=
  match point with
  | first => parent.firstRoot
  | second => parent.secondRoot
  | third => parent.thirdRoot

end DegreeSevenStageFiveCriticalPoint

/-- A compact certificate that a quartic cannot be both split and separable.
The recorded critical value has the opposite sign from the alternating sign
forced by four simple real roots. -/
structure DegreeSevenStageFiveCriticalSignWitness where
  parent : DegreeSevenStageFourEntry
  a3 : ℤ
  point : DegreeSevenStageFiveCriticalPoint
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveCriticalSignWitness

def coefficients
    (witness : DegreeSevenStageFiveCriticalSignWitness) : List ℤ :=
  [witness.a3, 4 * witness.parent.a4, 10 * witness.parent.a5,
    20 * witness.parent.a6, 35]

def criticalValueRange
    (witness : DegreeSevenStageFiveCriticalSignWitness) :
    LeanCert.Core.IntervalRat :=
  integerPolynomialRootIntervalEval witness.coefficients
    (witness.point.interval witness.parent)

/-- The parent cubic has a complete root certificate and the quartic value
on the selected root interval has the strictly contradictory sign. -/
def Valid (witness : DegreeSevenStageFiveCriticalSignWitness) : Prop :=
  witness.parent.Valid ∧
    match witness.point with
    | .first => 0 < witness.criticalValueRange.lo
    | .second => witness.criticalValueRange.hi < 0
    | .third => 0 < witness.criticalValueRange.lo

instance (witness : DegreeSevenStageFiveCriticalSignWitness) :
    Decidable witness.Valid := by
  unfold Valid DegreeSevenStageFourEntry.Valid
  cases witness.point <;> infer_instance

end DegreeSevenStageFiveCriticalSignWitness

/-- One complete finite split of a fourth-stage `a3` interval. -/
structure DegreeSevenStageFiveCoverage where
  parent : DegreeSevenStageFourEntry
  lower : ℤ
  upper : ℤ
  survivingA3 : List ℤ
  multipleRootA3Roots : List (ℤ × ℤ)
  criticalSignWitnesses :
    List DegreeSevenStageFiveCriticalSignWitness
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveCoverage

def rangeRecord (coverage : DegreeSevenStageFiveCoverage) :
    ℤ × ℤ × ℤ × ℤ × ℤ :=
  (coverage.parent.a6, coverage.parent.a5, coverage.parent.a4,
    coverage.lower, coverage.upper)

def topQuadruples (coverage : DegreeSevenStageFiveCoverage) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  coverage.survivingA3.map fun a3 =>
    (coverage.parent.a6, coverage.parent.a5, coverage.parent.a4, a3)

def multipleRootQuadruples (coverage : DegreeSevenStageFiveCoverage) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  coverage.multipleRootA3Roots.map fun pair =>
    (coverage.parent.a6, coverage.parent.a5, coverage.parent.a4, pair.1)

def criticalSignQuadruples (coverage : DegreeSevenStageFiveCoverage) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  coverage.criticalSignWitnesses.map fun witness =>
    (coverage.parent.a6, coverage.parent.a5, coverage.parent.a4,
      witness.a3)

def multipleRootWitnesses (coverage : DegreeSevenStageFiveCoverage) :
    List DegreeSevenStageFiveMultipleRootWitness :=
  coverage.multipleRootA3Roots.map fun pair =>
    ⟨coverage.parent.a6, coverage.parent.a5, coverage.parent.a4,
      pair.1, pair.2⟩

/-- The three recorded classes exhaust the exact integer interval attached
to the parent row, and every refined critical-sign certificate belongs to
that same parent coefficient row. -/
def Valid (coverage : DegreeSevenStageFiveCoverage) : Prop :=
  integerIcc coverage.lower coverage.upper =
      (coverage.survivingA3 ++
        coverage.multipleRootA3Roots.map Prod.fst ++
        coverage.criticalSignWitnesses.map
          DegreeSevenStageFiveCriticalSignWitness.a3).toFinset ∧
    coverage.criticalSignWitnesses.Forall fun witness ↦
      witness.parent.a6 = coverage.parent.a6 ∧
        witness.parent.a5 = coverage.parent.a5 ∧
        witness.parent.a4 = coverage.parent.a4

instance (coverage : DegreeSevenStageFiveCoverage) :
    Decidable coverage.Valid := by
  unfold Valid
  infer_instance

end DegreeSevenStageFiveCoverage

/-- A valid critical-sign witness rules out the simple totally real quartic
case.  This replaces a quartic discriminant calculation by the alternating
signs at its three ordered critical points. -/
theorem degreeSevenStageFiveCriticalSignWitness_not_splits_and_separable
    (witness : DegreeSevenStageFiveCriticalSignWitness)
    (hvalid : witness.Valid) :
    ¬((integerPolynomialReal witness.coefficients).Splits ∧
      (integerPolynomialReal witness.coefficients).Separable) := by
  rintro ⟨hqsplit, hqseparable⟩
  let q : ℝ[X] := integerPolynomialReal witness.coefficients
  let r : ℝ[X] :=
    integerPolynomialReal witness.parent.derivativeCoefficients
  have hparentValid : witness.parent.Valid := hvalid.1
  have hrsplit : r.Splits :=
    integerPolynomial_splits_of_generalRootIntervals hparentValid
  have hrdegree : r.natDegree = 3 :=
    integerPolynomial_natDegree_of_generalRootIntervals
      hparentValid.2.1 hparentValid.2.2.1
  have hqdegree : q.natDegree = 4 := by
    apply integerPolynomial_natDegree_of_generalRootIntervals
    · simp [DegreeSevenStageFiveCriticalSignWitness.coefficients]
    · norm_num [
        DegreeSevenStageFiveCriticalSignWitness.coefficients]
  have hqlead : 0 < q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hqdegree]
    change 0 <
      (integerPolynomialReal witness.coefficients).coeff 4
    rw [integerPolynomialReal, Polynomial.coeff_map,
      DensePolynomial.coeff_toPolynomial]
    norm_num [DegreeSevenStageFiveCriticalSignWitness.coefficients]
  have hqderivEq : q.derivative = C 4 * r := by
    simpa [q, r,
      DegreeSevenStageFiveCriticalSignWitness.coefficients,
      DegreeSevenStageFourEntry.derivativeCoefficients] using
      degreeSeven_quartic_derivative_eq witness.a3
        witness.parent.a4 witness.parent.a5 witness.parent.a6
  let ri : Fin r.natDegree :=
    ⟨witness.point.index, by rw [hrdegree]; exact witness.point.index.isLt⟩
  let qi : Fin q.derivative.natDegree :=
    ⟨ri, by
      rw [hqderivEq, Polynomial.natDegree_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)]
      exact ri.isLt⟩
  have hrootEq :
      voightSortedRoot q.derivative
          (splits_derivative_of_splits_real hqsplit) qi =
        voightSortedRoot r hrsplit ri := by
    simpa [qi] using
      voightSortedRoot_eq_of_eq_C_mul
        (by norm_num : (4 : ℝ) ≠ 0)
        (splits_derivative_of_splits_real hqsplit)
        hrsplit hqderivEq ri
  let parentIndex : Fin witness.parent.rootIntervals.length :=
    ⟨witness.point.index, by
      cases witness.point <;>
        simp [DegreeSevenStageFiveCriticalPoint.index,
          DegreeSevenStageFourEntry.rootIntervals]⟩
  have hrootMemRaw :=
    sortedRoot_mem_interval_of_generalRootIntervals
      hparentValid parentIndex
  have hrootMem : voightSortedRoot r hrsplit ri ∈
      Set.Icc
        ((witness.point.interval witness.parent).lower : ℝ)
        ((witness.point.interval witness.parent).upper : ℝ) := by
    cases hpoint : witness.point <;>
      simpa [r, ri, parentIndex,
        DegreeSevenStageFiveCriticalPoint.index,
        DegreeSevenStageFiveCriticalPoint.interval,
        DegreeSevenStageFourEntry.rootIntervals, hpoint] using hrootMemRaw
  have hordered :
      (witness.point.interval witness.parent).lower ≤
        (witness.point.interval witness.parent).upper := by
    have hintervals := List.forall_iff_forall_mem.mp
      hparentValid.2.2.2.2.1
    cases witness.point
    · exact (hintervals witness.parent.firstRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.secondRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])).1.le
    · exact (hintervals witness.parent.thirdRoot
        (by simp [DegreeSevenStageFourEntry.rootIntervals])).1.le
  have hvalue : q.eval (voightSortedRoot r hrsplit ri) ∈
      witness.criticalValueRange := by
    exact integerPolynomial_eval_mem_rootInterval
      witness.coefficients (witness.point.interval witness.parent)
      hordered hrootMem
  have hsign :=
    eval_sign_at_derivativeSortedRoot_of_leadingCoeff_pos
      hqsplit hqlead hqseparable qi
  rw [hrootEq] at hsign
  have hqdegree' :
      (integerPolynomialReal witness.coefficients).natDegree = 4 := by
    simpa [q] using hqdegree
  rw [hqdegree'] at hsign
  simp only [LeanCert.Core.IntervalRat.mem_def] at hvalue
  cases hpoint : witness.point
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) <
        (witness.criticalValueRange.lo : ℝ) := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri,
      DegreeSevenStageFiveCriticalPoint.index, hpoint] at hsign
    have hsign' :
        q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageFiveCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong :
        (witness.criticalValueRange.hi : ℝ) < 0 := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri,
      DegreeSevenStageFiveCriticalPoint.index, hpoint] at hsign
    have hsign' :
        0 ≤ q.eval (voightSortedRoot r hrsplit ri) := by
      simpa [q, ri, DegreeSevenStageFiveCriticalPoint.index,
        hpoint] using hsign
    linarith
  · have hwrongRat := hvalid.2
    simp only [hpoint] at hwrongRat
    have hwrong : (0 : ℝ) <
        (witness.criticalValueRange.lo : ℝ) := by
      exact_mod_cast hwrongRat
    norm_num [qi, ri,
      DegreeSevenStageFiveCriticalPoint.index, hpoint] at hsign
    have hsign' :
        q.eval (voightSortedRoot r hrsplit ri) ≤ 0 := by
      simpa [q, ri, DegreeSevenStageFiveCriticalPoint.index,
        hpoint] using hsign
    linarith

end

end TraceEuclidean
