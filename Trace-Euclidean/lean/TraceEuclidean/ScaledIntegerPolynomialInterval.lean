import TraceEuclidean.PolynomialIntervalEvaluation

/-!
# Cleared-denominator polynomial interval evaluation

For a rational input interval whose endpoints share a positive integer
denominator, Horner interval evaluation can be performed entirely in `ℤ`.
The result below proves that the integer endpoints, divided by the appropriate
power of the denominator, are exactly the existing rational interval result.
-/

namespace TraceEuclidean

open LeanCert.Core

/-- Minimum of four integers. -/
def integerMin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)

/-- Maximum of four integers. -/
def integerMax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- Integer Horner interval numerators.  A coefficient list of length `n`
returns endpoints with common denominator `denominator ^ n`. -/
def scaledIntegerPolynomialIntervalEval (denominator inputLower inputUpper : ℤ) :
    List ℤ → ℤ × ℤ
  | [] => (0, 0)
  | coefficient :: coefficients =>
      let tail := scaledIntegerPolynomialIntervalEval
        denominator inputLower inputUpper coefficients
      let productLower := integerMin4
        (inputLower * tail.1) (inputLower * tail.2)
        (inputUpper * tail.1) (inputUpper * tail.2)
      let productUpper := integerMax4
        (inputLower * tail.1) (inputLower * tail.2)
        (inputUpper * tail.1) (inputUpper * tail.2)
      let scale := denominator ^ (coefficients.length + 1)
      (coefficient * scale + productLower,
        coefficient * scale + productUpper)

private theorem min_div_pos (a b : ℤ) (d : ℚ) (hd : 0 < d) :
    min ((a : ℚ) / d) ((b : ℚ) / d) = ((min a b : ℤ) : ℚ) / d := by
  by_cases h : a ≤ b
  · have hq : (a : ℚ) / d ≤ (b : ℚ) / d := by
      rw [div_le_div_iff_of_pos_right hd]
      exact_mod_cast h
    rw [min_eq_left hq, min_eq_left h]
  · have h' : b ≤ a := le_of_lt (lt_of_not_ge h)
    have hq : (b : ℚ) / d ≤ (a : ℚ) / d := by
      rw [div_le_div_iff_of_pos_right hd]
      exact_mod_cast h'
    rw [min_eq_right hq, min_eq_right h']

private theorem max_div_pos (a b : ℤ) (d : ℚ) (hd : 0 < d) :
    max ((a : ℚ) / d) ((b : ℚ) / d) = ((max a b : ℤ) : ℚ) / d := by
  by_cases h : a ≤ b
  · have hq : (a : ℚ) / d ≤ (b : ℚ) / d := by
      rw [div_le_div_iff_of_pos_right hd]
      exact_mod_cast h
    rw [max_eq_right hq, max_eq_right h]
  · have h' : b ≤ a := le_of_lt (lt_of_not_ge h)
    have hq : (b : ℚ) / d ≤ (a : ℚ) / d := by
      rw [div_le_div_iff_of_pos_right hd]
      exact_mod_cast h'
    rw [max_eq_left hq, max_eq_left h']

private theorem min4_div_pos (a b c d : ℤ) (q : ℚ) (hq : 0 < q) :
    IntervalRat.min4 ((a : ℚ) / q) ((b : ℚ) / q)
        ((c : ℚ) / q) ((d : ℚ) / q) =
      ((integerMin4 a b c d : ℤ) : ℚ) / q := by
  simp only [IntervalRat.min4, integerMin4]
  rw [min_div_pos a b q hq, min_div_pos c d q hq,
    min_div_pos (min a b) (min c d) q hq]

private theorem max4_div_pos (a b c d : ℤ) (q : ℚ) (hq : 0 < q) :
    IntervalRat.max4 ((a : ℚ) / q) ((b : ℚ) / q)
        ((c : ℚ) / q) ((d : ℚ) / q) =
      ((integerMax4 a b c d : ℤ) : ℚ) / q := by
  simp only [IntervalRat.max4, integerMax4]
  rw [max_div_pos a b q hq, max_div_pos c d q hq,
    max_div_pos (max a b) (max c d) q hq]

private theorem mul_div_pow (a b denominator : ℤ) (n : ℕ)
    (hdenominator : 0 < denominator) :
    ((a : ℚ) / denominator) * ((b : ℚ) / denominator ^ n) =
      ((a * b : ℤ) : ℚ) / denominator ^ (n + 1) := by
  have hne : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdenominator
  push_cast
  field_simp
  ring

/-- Correctness of the cleared-denominator evaluator. -/
theorem scaledIntegerPolynomialIntervalEval_correct
    (coefficients : List ℤ) (denominator inputLower inputUpper : ℤ)
    (hdenominator : 0 < denominator) (hinput : inputLower ≤ inputUpper) :
    let input : IntervalRat :=
      ⟨(inputLower : ℚ) / denominator,
        (inputUpper : ℚ) / denominator, by
          rw [div_le_div_iff_of_pos_right (by exact_mod_cast hdenominator)]
          exact_mod_cast hinput⟩
    let result := denseRationalPolynomialIntervalEval
      (coefficients.map (Int.castRingHom ℚ)) input
    let scaled := scaledIntegerPolynomialIntervalEval
      denominator inputLower inputUpper coefficients
    result.lo = (scaled.1 : ℚ) / denominator ^ coefficients.length ∧
      result.hi = (scaled.2 : ℚ) / denominator ^ coefficients.length := by
  induction coefficients generalizing denominator inputLower inputUpper with
  | nil =>
      simp [denseRationalPolynomialIntervalEval,
        scaledIntegerPolynomialIntervalEval, IntervalRat.singleton]
  | cons coefficient coefficients induction =>
      dsimp only [List.map_cons, List.length_cons,
        denseRationalPolynomialIntervalEval,
        scaledIntegerPolynomialIntervalEval]
      have hdenominatorRat : (0 : ℚ) < denominator := by
        exact_mod_cast hdenominator
      have hpow : (0 : ℚ) < (denominator : ℚ) ^ (coefficients.length + 1) :=
        pow_pos hdenominatorRat _
      have hinduction := induction denominator inputLower inputUpper
        hdenominator hinput
      dsimp only at hinduction
      rcases hinduction with ⟨hlower, hupper⟩
      simp only [IntervalRat.add, IntervalRat.singleton,
        IntervalRat.mul]
      rw [hlower, hupper]
      have hll := mul_div_pow inputLower
        (scaledIntegerPolynomialIntervalEval
          denominator inputLower inputUpper coefficients).1
        denominator coefficients.length hdenominator
      have hlu := mul_div_pow inputLower
        (scaledIntegerPolynomialIntervalEval
          denominator inputLower inputUpper coefficients).2
        denominator coefficients.length hdenominator
      have hul := mul_div_pow inputUpper
        (scaledIntegerPolynomialIntervalEval
          denominator inputLower inputUpper coefficients).1
        denominator coefficients.length hdenominator
      have huu := mul_div_pow inputUpper
        (scaledIntegerPolynomialIntervalEval
          denominator inputLower inputUpper coefficients).2
        denominator coefficients.length hdenominator
      rw [hll, hlu, hul, huu]
      rw [min4_div_pos _ _ _ _ _ hpow,
        max4_div_pos _ _ _ _ _ hpow]
      have hne : (denominator : ℚ) ≠ 0 := ne_of_gt hdenominatorRat
      constructor <;> push_cast <;> field_simp <;> simp <;> ring

/-- Endpoint form of the cleared-denominator correctness theorem.  It allows
callers to reuse an existing rational interval instead of rebuilding the
canonical interval record. -/
theorem scaledIntegerPolynomialIntervalEval_correct_of_endpoints
    (coefficients : List ℤ) (input : IntervalRat)
    (denominator inputLower inputUpper : ℤ)
    (hdenominator : 0 < denominator)
    (hlower : input.lo = (inputLower : ℚ) / denominator)
    (hupper : input.hi = (inputUpper : ℚ) / denominator) :
    let scaled := scaledIntegerPolynomialIntervalEval
      denominator inputLower inputUpper coefficients
    (integerPolynomialIntervalEval coefficients input).lo =
        (scaled.1 : ℚ) / denominator ^ coefficients.length ∧
      (integerPolynomialIntervalEval coefficients input).hi =
        (scaled.2 : ℚ) / denominator ^ coefficients.length := by
  have hdenominatorRat : (0 : ℚ) < denominator := by
    exact_mod_cast hdenominator
  have hinputOrder : inputLower ≤ inputUpper := by
    have h := input.le
    rw [hlower, hupper, div_le_div_iff_of_pos_right hdenominatorRat] at h
    exact_mod_cast h
  let canonicalInput : IntervalRat :=
    ⟨(inputLower : ℚ) / denominator,
      (inputUpper : ℚ) / denominator, by
        rw [div_le_div_iff_of_pos_right hdenominatorRat]
        exact_mod_cast hinputOrder⟩
  have hinput : input = canonicalInput := by
    cases input
    simp_all [canonicalInput]
  rw [hinput]
  simpa only [integerPolynomialIntervalEval] using
    scaledIntegerPolynomialIntervalEval_correct coefficients denominator
      inputLower inputUpper hdenominator hinputOrder

end TraceEuclidean
