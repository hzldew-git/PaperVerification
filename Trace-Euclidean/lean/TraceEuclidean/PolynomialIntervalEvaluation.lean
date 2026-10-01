import LeanCert.Core.IntervalRat.Basic
import TraceEuclidean.GeneralRootIntervalCertificate

/-!
# Exact interval evaluation for dense rational polynomials

Voight's coefficient recursion evaluates an antiderivative at roots of the
next derivative stage.  Those roots are represented by rational isolating
intervals.  This module supplies a small Horner interval evaluator and proves
that its rational output encloses the exact real value.  It uses only the
fundamental interval operations already proved in `LeanCert`.
-/

namespace TraceEuclidean

open LeanCert.Core

namespace DensePolynomial

/-- Formal derivative of an ascending dense coefficient list. -/
def derivative {R : Type*} [CommSemiring R] : List R → List R
  | [] => []
  | _ :: coefficients => add coefficients (0 :: derivative coefficients)

/-- The dense derivative represents the usual polynomial derivative. -/
@[simp]
theorem toPolynomial_derivative {R : Type*} [CommSemiring R]
    (coefficients : List R) :
    toPolynomial (derivative coefficients) =
      (toPolynomial coefficients).derivative := by
  induction coefficients with
  | nil => simp [derivative]
  | cons coefficient coefficients induction =>
      simp [derivative, induction, Polynomial.derivative_add,
        Polynomial.derivative_mul]

end DensePolynomial

/-- The real interpretation of the dense derivative is the derivative of the
real interpretation. -/
theorem integerPolynomialReal_derivative (coefficients : List ℤ) :
    (integerPolynomialReal coefficients).derivative =
      integerPolynomialReal
        (DensePolynomial.derivative coefficients) := by
  simp [integerPolynomialReal]

/-- Horner interval evaluation of an ascending rational coefficient list. -/
def denseRationalPolynomialIntervalEval :
    List ℚ → IntervalRat → IntervalRat
  | [], _ => IntervalRat.singleton 0
  | coefficient :: coefficients, input =>
      IntervalRat.add (IntervalRat.singleton coefficient)
        (IntervalRat.mul input
          (denseRationalPolynomialIntervalEval coefficients input))

/-- Correctness of the rational Horner interval evaluator. -/
theorem denseRationalPolynomial_eval_mem_interval
    (coefficients : List ℚ) (input : IntervalRat)
    {x : ℝ} (hx : x ∈ input) :
    DensePolynomial.eval
        (coefficients.map (algebraMap ℚ ℝ)) x ∈
      denseRationalPolynomialIntervalEval coefficients input := by
  induction coefficients with
  | nil =>
      simpa [DensePolynomial.eval,
        denseRationalPolynomialIntervalEval] using
        IntervalRat.mem_singleton 0
  | cons coefficient coefficients induction =>
      simp only [List.map_cons, DensePolynomial.eval,
        denseRationalPolynomialIntervalEval]
      exact IntervalRat.mem_add (IntervalRat.mem_singleton coefficient)
        (IntervalRat.mem_mul hx induction)

/-- Exact interval evaluation for a dense integer polynomial. -/
def integerPolynomialIntervalEval
    (coefficients : List ℤ) (input : IntervalRat) : IntervalRat :=
  denseRationalPolynomialIntervalEval
    (coefficients.map (Int.castRingHom ℚ)) input

/-- The real value of a dense integer polynomial belongs to its computed
rational Horner interval. -/
theorem integerPolynomial_eval_mem_interval
    (coefficients : List ℤ) (input : IntervalRat)
    {x : ℝ} (hx : x ∈ input) :
    (integerPolynomialReal coefficients).eval x ∈
      integerPolynomialIntervalEval coefficients input := by
  rw [integerPolynomialReal,
    ← DensePolynomial.toPolynomial_map,
    DensePolynomial.eval_toPolynomial]
  change DensePolynomial.eval
      (coefficients.map (Int.castRingHom ℝ)) x ∈ _
  rw [show coefficients.map (Int.castRingHom ℝ) =
      (coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ) by simp]
  exact denseRationalPolynomial_eval_mem_interval
    (coefficients.map (Int.castRingHom ℚ)) input hx

/-- Interpret a root interval as a `LeanCert` rational interval.  Invalid
endpoint order falls back to the singleton zero interval; certificate
validity rules out that branch. -/
def RationalRootInterval.toIntervalRat
    (interval : RationalRootInterval) : IntervalRat :=
  if h : interval.lower ≤ interval.upper then
    ⟨interval.lower, interval.upper, h⟩
  else
    IntervalRat.singleton 0

/-- Membership in an ordered root interval agrees with membership in its
`LeanCert` interval interpretation. -/
theorem RationalRootInterval.mem_toIntervalRat
    (interval : RationalRootInterval)
    (hordered : interval.lower ≤ interval.upper) {x : ℝ}
    (hx : x ∈ Set.Icc (interval.lower : ℝ) (interval.upper : ℝ)) :
    x ∈ interval.toIntervalRat := by
  simp only [RationalRootInterval.toIntervalRat, hordered,
    ↓reduceDIte, IntervalRat.mem_def]
  exact hx

/-- Evaluate a dense integer polynomial on one rational root interval. -/
def integerPolynomialRootIntervalEval
    (coefficients : List ℤ) (interval : RationalRootInterval) :
    IntervalRat :=
  integerPolynomialIntervalEval coefficients interval.toIntervalRat

/-- The interval evaluator encloses the polynomial value at every real point
in an ordered rational root interval. -/
theorem integerPolynomial_eval_mem_rootInterval
    (coefficients : List ℤ) (interval : RationalRootInterval)
    (hordered : interval.lower ≤ interval.upper) {x : ℝ}
    (hx : x ∈ Set.Icc (interval.lower : ℝ) (interval.upper : ℝ)) :
    (integerPolynomialReal coefficients).eval x ∈
      integerPolynomialRootIntervalEval coefficients interval := by
  exact integerPolynomial_eval_mem_interval coefficients
    interval.toIntervalRat
    (RationalRootInterval.mem_toIntervalRat interval hordered hx)

end TraceEuclidean
