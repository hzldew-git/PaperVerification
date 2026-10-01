import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import TraceEuclidean.PolynomialIntervalEvaluation
import TraceEuclidean.VoightRollePruning

/-!
# Exact coefficient pruning for the Voight recursion

At one recursion step a polynomial has the form `g + a`, where `a` is the
next integer coefficient.  Alternating signs at the derivative roots and at
two outer endpoints bound `a`.  This module converts interval enclosures for
the values of `g` into executable integer bounds.

The first theorem treats the cubic step used in the quintic enumeration.  Its
proof contains no floating point computation: rational Horner intervals are
rounded with the mathematical floor and ceiling operations.
-/

namespace TraceEuclidean

open LeanCert.Core Polynomial

/-- The lower integer bound at a cubic translation step. -/
def cubicTranslationLowerBound (baseCoefficients : List ℤ)
    (firstRoot : RationalRootInterval) (rightEndpoint : ℚ) : ℤ :=
  max
    (Int.ceil (-(integerPolynomialRootIntervalEval
      baseCoefficients firstRoot).hi))
    (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton rightEndpoint)).hi))

/-- The upper integer bound at a cubic translation step. -/
def cubicTranslationUpperBound (baseCoefficients : List ℤ)
    (leftEndpoint : ℚ)
    (secondRoot : RationalRootInterval) : ℤ :=
  min
    (Int.floor (-(integerPolynomialRootIntervalEval
      baseCoefficients secondRoot).lo))
    (Int.floor (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton leftEndpoint)).lo))

/-- A computable closed integer interval with an explicit order instance. -/
def integerIcc (lower upper : ℤ) : Finset ℤ :=
  @Finset.Icc ℤ Int.instLinearOrder.toPreorder
    Int.instLocallyFiniteOrder lower upper

/-- The finite set of integer translations surviving the exact cubic sign
test. -/
def cubicTranslationCandidates (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot : RationalRootInterval) : Finset ℤ :=
  integerIcc
    (cubicTranslationLowerBound
      baseCoefficients firstRoot rightEndpoint)
    (cubicTranslationUpperBound
      baseCoefficients leftEndpoint secondRoot)

/-- Alternating real signs at two cubic critical points and the two outer
endpoints force the integer translation into the computed candidate set. -/
theorem mem_cubicTranslationCandidates_of_signs
    (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot : RationalRootInterval)
    (hfirstOrdered : firstRoot.lower ≤ firstRoot.upper)
    (hsecondOrdered : secondRoot.lower ≤ secondRoot.upper)
    (firstValue secondValue : ℝ)
    (hfirstMem : firstValue ∈
      Set.Icc (firstRoot.lower : ℝ) (firstRoot.upper : ℝ))
    (hsecondMem : secondValue ∈
      Set.Icc (secondRoot.lower : ℝ) (secondRoot.upper : ℝ))
    (coefficient : ℤ)
    (hleftSign :
      (integerPolynomialReal baseCoefficients).eval
          (leftEndpoint : ℝ) + coefficient ≤ 0)
    (hfirstSign :
      0 ≤ (integerPolynomialReal baseCoefficients).eval firstValue +
        coefficient)
    (hsecondSign :
      (integerPolynomialReal baseCoefficients).eval secondValue +
          coefficient ≤ 0)
    (hrightSign :
      0 ≤ (integerPolynomialReal baseCoefficients).eval
        (rightEndpoint : ℝ) + coefficient) :
    coefficient ∈ cubicTranslationCandidates baseCoefficients
      leftEndpoint rightEndpoint firstRoot secondRoot := by
  have hfirstRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients firstRoot hfirstOrdered hfirstMem
  have hsecondRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients secondRoot hsecondOrdered hsecondMem
  have hleftRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton leftEndpoint)
    (IntervalRat.mem_singleton leftEndpoint)
  have hrightRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton rightEndpoint)
    (IntervalRat.mem_singleton rightEndpoint)
  rw [cubicTranslationCandidates, integerIcc, Finset.mem_Icc]
  constructor
  · rw [cubicTranslationLowerBound, max_le_iff]
    constructor
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialRootIntervalEval
            baseCoefficients firstRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hfirstRange
        linarith
      exact_mod_cast hreal
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialIntervalEval baseCoefficients
            (IntervalRat.singleton rightEndpoint)).hi : ℝ)) ≤
            coefficient := by
        rw [IntervalRat.mem_def] at hrightRange
        linarith
      exact_mod_cast hreal
  · rw [cubicTranslationUpperBound, le_min_iff]
    constructor
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients secondRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hsecondRange
        linarith
      exact_mod_cast hreal
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialIntervalEval baseCoefficients
              (IntervalRat.singleton leftEndpoint)).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hleftRange
        linarith
      exact_mod_cast hreal

/-- The lower integer bound at a quartic translation step. -/
def quarticTranslationLowerBound (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (secondRoot : RationalRootInterval) : ℤ :=
  max
    (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton leftEndpoint)).hi))
    (max
      (Int.ceil (-(integerPolynomialRootIntervalEval
        baseCoefficients secondRoot).hi))
      (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
        (IntervalRat.singleton rightEndpoint)).hi)))

/-- The upper integer bound at a quartic translation step. -/
def quarticTranslationUpperBound (baseCoefficients : List ℤ)
    (firstRoot thirdRoot : RationalRootInterval) : ℤ :=
  min
    (Int.floor (-(integerPolynomialRootIntervalEval
      baseCoefficients firstRoot).lo))
    (Int.floor (-(integerPolynomialRootIntervalEval
      baseCoefficients thirdRoot).lo))

/-- The finite set of integer translations surviving the exact quartic sign
test. -/
def quarticTranslationCandidates (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot : RationalRootInterval) :
    Finset ℤ :=
  integerIcc
    (quarticTranslationLowerBound baseCoefficients
      leftEndpoint rightEndpoint secondRoot)
    (quarticTranslationUpperBound baseCoefficients
      firstRoot thirdRoot)

/-- Alternating real signs at three quartic critical points and the two outer
endpoints force the integer translation into the computed candidate set. -/
theorem mem_quarticTranslationCandidates_of_signs
    (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot : RationalRootInterval)
    (hfirstOrdered : firstRoot.lower ≤ firstRoot.upper)
    (hsecondOrdered : secondRoot.lower ≤ secondRoot.upper)
    (hthirdOrdered : thirdRoot.lower ≤ thirdRoot.upper)
    (firstValue secondValue thirdValue : ℝ)
    (hfirstMem : firstValue ∈
      Set.Icc (firstRoot.lower : ℝ) (firstRoot.upper : ℝ))
    (hsecondMem : secondValue ∈
      Set.Icc (secondRoot.lower : ℝ) (secondRoot.upper : ℝ))
    (hthirdMem : thirdValue ∈
      Set.Icc (thirdRoot.lower : ℝ) (thirdRoot.upper : ℝ))
    (coefficient : ℤ)
    (hleftSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval
          (leftEndpoint : ℝ) + coefficient)
    (hfirstSign :
      (integerPolynomialReal baseCoefficients).eval firstValue +
          coefficient ≤ 0)
    (hsecondSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval secondValue +
        coefficient)
    (hthirdSign :
      (integerPolynomialReal baseCoefficients).eval thirdValue +
          coefficient ≤ 0)
    (hrightSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval
          (rightEndpoint : ℝ) + coefficient) :
    coefficient ∈ quarticTranslationCandidates baseCoefficients
      leftEndpoint rightEndpoint firstRoot secondRoot thirdRoot := by
  have hfirstRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients firstRoot hfirstOrdered hfirstMem
  have hsecondRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients secondRoot hsecondOrdered hsecondMem
  have hthirdRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients thirdRoot hthirdOrdered hthirdMem
  have hleftRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton leftEndpoint)
    (IntervalRat.mem_singleton leftEndpoint)
  have hrightRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton rightEndpoint)
    (IntervalRat.mem_singleton rightEndpoint)
  rw [quarticTranslationCandidates, integerIcc, Finset.mem_Icc]
  constructor
  · rw [quarticTranslationLowerBound, max_le_iff, max_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialIntervalEval baseCoefficients
            (IntervalRat.singleton leftEndpoint)).hi : ℝ)) ≤
            coefficient := by
        rw [IntervalRat.mem_def] at hleftRange
        linarith
      exact_mod_cast hreal
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialRootIntervalEval
            baseCoefficients secondRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hsecondRange
        linarith
      exact_mod_cast hreal
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialIntervalEval baseCoefficients
            (IntervalRat.singleton rightEndpoint)).hi : ℝ)) ≤
            coefficient := by
        rw [IntervalRat.mem_def] at hrightRange
        linarith
      exact_mod_cast hreal
  · rw [quarticTranslationUpperBound, le_min_iff]
    constructor
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients firstRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hfirstRange
        linarith
      exact_mod_cast hreal
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients thirdRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hthirdRange
        linarith
      exact_mod_cast hreal

/-- The lower integer bound at a quintic translation step. -/
def quinticTranslationLowerBound (baseCoefficients : List ℤ)
    (rightEndpoint : ℚ)
    (firstRoot thirdRoot : RationalRootInterval) : ℤ :=
  max
    (Int.ceil (-(integerPolynomialRootIntervalEval
      baseCoefficients firstRoot).hi))
    (max
      (Int.ceil (-(integerPolynomialRootIntervalEval
        baseCoefficients thirdRoot).hi))
      (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
        (IntervalRat.singleton rightEndpoint)).hi)))

/-- The upper integer bound at a quintic translation step. -/
def quinticTranslationUpperBound (baseCoefficients : List ℤ)
    (leftEndpoint : ℚ)
    (secondRoot fourthRoot : RationalRootInterval) : ℤ :=
  min
    (Int.floor (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton leftEndpoint)).lo))
    (min
      (Int.floor (-(integerPolynomialRootIntervalEval
        baseCoefficients secondRoot).lo))
      (Int.floor (-(integerPolynomialRootIntervalEval
        baseCoefficients fourthRoot).lo)))

/-- The finite set of integer translations surviving the exact quintic sign
test. -/
def quinticTranslationCandidates (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot : RationalRootInterval) :
    Finset ℤ :=
  integerIcc
    (quinticTranslationLowerBound baseCoefficients
      rightEndpoint firstRoot thirdRoot)
    (quinticTranslationUpperBound baseCoefficients
      leftEndpoint secondRoot fourthRoot)

/-- Alternating real signs at four quintic critical points and the two outer
endpoints force the integer translation into the computed candidate set. -/
theorem mem_quinticTranslationCandidates_of_signs
    (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot : RationalRootInterval)
    (hfirstOrdered : firstRoot.lower ≤ firstRoot.upper)
    (hsecondOrdered : secondRoot.lower ≤ secondRoot.upper)
    (hthirdOrdered : thirdRoot.lower ≤ thirdRoot.upper)
    (hfourthOrdered : fourthRoot.lower ≤ fourthRoot.upper)
    (firstValue secondValue thirdValue fourthValue : ℝ)
    (hfirstMem : firstValue ∈
      Set.Icc (firstRoot.lower : ℝ) (firstRoot.upper : ℝ))
    (hsecondMem : secondValue ∈
      Set.Icc (secondRoot.lower : ℝ) (secondRoot.upper : ℝ))
    (hthirdMem : thirdValue ∈
      Set.Icc (thirdRoot.lower : ℝ) (thirdRoot.upper : ℝ))
    (hfourthMem : fourthValue ∈
      Set.Icc (fourthRoot.lower : ℝ) (fourthRoot.upper : ℝ))
    (coefficient : ℤ)
    (hleftSign :
      (integerPolynomialReal baseCoefficients).eval
          (leftEndpoint : ℝ) + coefficient ≤ 0)
    (hfirstSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval firstValue +
        coefficient)
    (hsecondSign :
      (integerPolynomialReal baseCoefficients).eval secondValue +
          coefficient ≤ 0)
    (hthirdSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval thirdValue +
        coefficient)
    (hfourthSign :
      (integerPolynomialReal baseCoefficients).eval fourthValue +
          coefficient ≤ 0)
    (hrightSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval
          (rightEndpoint : ℝ) + coefficient) :
    coefficient ∈ quinticTranslationCandidates baseCoefficients
      leftEndpoint rightEndpoint firstRoot secondRoot thirdRoot fourthRoot := by
  have hfirstRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients firstRoot hfirstOrdered hfirstMem
  have hsecondRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients secondRoot hsecondOrdered hsecondMem
  have hthirdRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients thirdRoot hthirdOrdered hthirdMem
  have hfourthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients fourthRoot hfourthOrdered hfourthMem
  have hleftRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton leftEndpoint)
    (IntervalRat.mem_singleton leftEndpoint)
  have hrightRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton rightEndpoint)
    (IntervalRat.mem_singleton rightEndpoint)
  rw [quinticTranslationCandidates, integerIcc, Finset.mem_Icc]
  constructor
  · rw [quinticTranslationLowerBound, max_le_iff, max_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialRootIntervalEval
            baseCoefficients firstRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hfirstRange
        linarith
      exact_mod_cast hreal
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialRootIntervalEval
            baseCoefficients thirdRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hthirdRange
        linarith
      exact_mod_cast hreal
    · rw [Int.ceil_le]
      have hreal :
          (-((integerPolynomialIntervalEval baseCoefficients
            (IntervalRat.singleton rightEndpoint)).hi : ℝ)) ≤
            coefficient := by
        rw [IntervalRat.mem_def] at hrightRange
        linarith
      exact_mod_cast hreal
  · rw [quinticTranslationUpperBound, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialIntervalEval baseCoefficients
              (IntervalRat.singleton leftEndpoint)).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hleftRange
        linarith
      exact_mod_cast hreal
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients secondRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hsecondRange
        linarith
      exact_mod_cast hreal
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients fourthRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hfourthRange
        linarith
      exact_mod_cast hreal

end TraceEuclidean
