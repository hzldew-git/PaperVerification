import TraceEuclidean.VoightCoefficientPruning

/-!
# Higher exact coefficient pruning for the Voight recursion

This module extends the exact translation bounds from cubic, quartic, and
quintic stages to the sextic and septic stages needed by the degree-seven
Hunter--Rolle enumeration.  Every bound is computed from rational isolating
intervals and mathematical floor or ceiling operations.
-/

namespace TraceEuclidean

open LeanCert.Core Polynomial

/-- The lower integer bound at a sextic translation step. -/
def sexticTranslationLowerBound (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (secondRoot fourthRoot : RationalRootInterval) : ℤ :=
  max
    (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton leftEndpoint)).hi))
    (max
      (Int.ceil (-(integerPolynomialRootIntervalEval
        baseCoefficients secondRoot).hi))
      (max
        (Int.ceil (-(integerPolynomialRootIntervalEval
          baseCoefficients fourthRoot).hi))
        (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
          (IntervalRat.singleton rightEndpoint)).hi))))

/-- The upper integer bound at a sextic translation step. -/
def sexticTranslationUpperBound (baseCoefficients : List ℤ)
    (firstRoot thirdRoot fifthRoot : RationalRootInterval) : ℤ :=
  min
    (Int.floor (-(integerPolynomialRootIntervalEval
      baseCoefficients firstRoot).lo))
    (min
      (Int.floor (-(integerPolynomialRootIntervalEval
        baseCoefficients thirdRoot).lo))
      (Int.floor (-(integerPolynomialRootIntervalEval
        baseCoefficients fifthRoot).lo)))

/-- The finite set of integer translations surviving the exact sextic sign
test. -/
def sexticTranslationCandidates (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot fifthRoot :
      RationalRootInterval) : Finset ℤ :=
  integerIcc
    (sexticTranslationLowerBound baseCoefficients leftEndpoint
      rightEndpoint secondRoot fourthRoot)
    (sexticTranslationUpperBound baseCoefficients firstRoot thirdRoot
      fifthRoot)

/-- Alternating real signs at five sextic critical points and the two outer
endpoints force the integer translation into the computed candidate set. -/
theorem mem_sexticTranslationCandidates_of_signs
    (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot fifthRoot :
      RationalRootInterval)
    (hfirstOrdered : firstRoot.lower ≤ firstRoot.upper)
    (hsecondOrdered : secondRoot.lower ≤ secondRoot.upper)
    (hthirdOrdered : thirdRoot.lower ≤ thirdRoot.upper)
    (hfourthOrdered : fourthRoot.lower ≤ fourthRoot.upper)
    (hfifthOrdered : fifthRoot.lower ≤ fifthRoot.upper)
    (firstValue secondValue thirdValue fourthValue fifthValue : ℝ)
    (hfirstMem : firstValue ∈
      Set.Icc (firstRoot.lower : ℝ) (firstRoot.upper : ℝ))
    (hsecondMem : secondValue ∈
      Set.Icc (secondRoot.lower : ℝ) (secondRoot.upper : ℝ))
    (hthirdMem : thirdValue ∈
      Set.Icc (thirdRoot.lower : ℝ) (thirdRoot.upper : ℝ))
    (hfourthMem : fourthValue ∈
      Set.Icc (fourthRoot.lower : ℝ) (fourthRoot.upper : ℝ))
    (hfifthMem : fifthValue ∈
      Set.Icc (fifthRoot.lower : ℝ) (fifthRoot.upper : ℝ))
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
    (hfourthSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval fourthValue +
        coefficient)
    (hfifthSign :
      (integerPolynomialReal baseCoefficients).eval fifthValue +
          coefficient ≤ 0)
    (hrightSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval
          (rightEndpoint : ℝ) + coefficient) :
    coefficient ∈ sexticTranslationCandidates baseCoefficients
      leftEndpoint rightEndpoint firstRoot secondRoot thirdRoot fourthRoot
      fifthRoot := by
  have hfirstRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients firstRoot hfirstOrdered hfirstMem
  have hsecondRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients secondRoot hsecondOrdered hsecondMem
  have hthirdRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients thirdRoot hthirdOrdered hthirdMem
  have hfourthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients fourthRoot hfourthOrdered hfourthMem
  have hfifthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients fifthRoot hfifthOrdered hfifthMem
  have hleftRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton leftEndpoint)
    (IntervalRat.mem_singleton leftEndpoint)
  have hrightRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton rightEndpoint)
    (IntervalRat.mem_singleton rightEndpoint)
  rw [sexticTranslationCandidates, integerIcc, Finset.mem_Icc]
  constructor
  · rw [sexticTranslationLowerBound, max_le_iff, max_le_iff,
      max_le_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
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
          (-((integerPolynomialRootIntervalEval
            baseCoefficients fourthRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hfourthRange
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
  · rw [sexticTranslationUpperBound, le_min_iff, le_min_iff]
    refine ⟨?_, ?_, ?_⟩
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
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients fifthRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hfifthRange
        linarith
      exact_mod_cast hreal

/-- The lower integer bound at a septic translation step. -/
def septicTranslationLowerBound (baseCoefficients : List ℤ)
    (rightEndpoint : ℚ)
    (firstRoot thirdRoot fifthRoot : RationalRootInterval) : ℤ :=
  max
    (Int.ceil (-(integerPolynomialRootIntervalEval
      baseCoefficients firstRoot).hi))
    (max
      (Int.ceil (-(integerPolynomialRootIntervalEval
        baseCoefficients thirdRoot).hi))
      (max
        (Int.ceil (-(integerPolynomialRootIntervalEval
          baseCoefficients fifthRoot).hi))
        (Int.ceil (-(integerPolynomialIntervalEval baseCoefficients
          (IntervalRat.singleton rightEndpoint)).hi))))

/-- The upper integer bound at a septic translation step. -/
def septicTranslationUpperBound (baseCoefficients : List ℤ)
    (leftEndpoint : ℚ)
    (secondRoot fourthRoot sixthRoot : RationalRootInterval) : ℤ :=
  min
    (Int.floor (-(integerPolynomialIntervalEval baseCoefficients
      (IntervalRat.singleton leftEndpoint)).lo))
    (min
      (Int.floor (-(integerPolynomialRootIntervalEval
        baseCoefficients secondRoot).lo))
      (min
        (Int.floor (-(integerPolynomialRootIntervalEval
          baseCoefficients fourthRoot).lo))
        (Int.floor (-(integerPolynomialRootIntervalEval
          baseCoefficients sixthRoot).lo))))

/-- The finite set of integer translations surviving the exact septic sign
test. -/
def septicTranslationCandidates (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot fifthRoot sixthRoot :
      RationalRootInterval) : Finset ℤ :=
  integerIcc
    (septicTranslationLowerBound baseCoefficients rightEndpoint
      firstRoot thirdRoot fifthRoot)
    (septicTranslationUpperBound baseCoefficients leftEndpoint
      secondRoot fourthRoot sixthRoot)

/-- Alternating real signs at six septic critical points and the two outer
endpoints force the integer translation into the computed candidate set. -/
theorem mem_septicTranslationCandidates_of_signs
    (baseCoefficients : List ℤ)
    (leftEndpoint rightEndpoint : ℚ)
    (firstRoot secondRoot thirdRoot fourthRoot fifthRoot sixthRoot :
      RationalRootInterval)
    (hfirstOrdered : firstRoot.lower ≤ firstRoot.upper)
    (hsecondOrdered : secondRoot.lower ≤ secondRoot.upper)
    (hthirdOrdered : thirdRoot.lower ≤ thirdRoot.upper)
    (hfourthOrdered : fourthRoot.lower ≤ fourthRoot.upper)
    (hfifthOrdered : fifthRoot.lower ≤ fifthRoot.upper)
    (hsixthOrdered : sixthRoot.lower ≤ sixthRoot.upper)
    (firstValue secondValue thirdValue fourthValue fifthValue sixthValue : ℝ)
    (hfirstMem : firstValue ∈
      Set.Icc (firstRoot.lower : ℝ) (firstRoot.upper : ℝ))
    (hsecondMem : secondValue ∈
      Set.Icc (secondRoot.lower : ℝ) (secondRoot.upper : ℝ))
    (hthirdMem : thirdValue ∈
      Set.Icc (thirdRoot.lower : ℝ) (thirdRoot.upper : ℝ))
    (hfourthMem : fourthValue ∈
      Set.Icc (fourthRoot.lower : ℝ) (fourthRoot.upper : ℝ))
    (hfifthMem : fifthValue ∈
      Set.Icc (fifthRoot.lower : ℝ) (fifthRoot.upper : ℝ))
    (hsixthMem : sixthValue ∈
      Set.Icc (sixthRoot.lower : ℝ) (sixthRoot.upper : ℝ))
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
    (hfifthSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval fifthValue +
        coefficient)
    (hsixthSign :
      (integerPolynomialReal baseCoefficients).eval sixthValue +
          coefficient ≤ 0)
    (hrightSign : 0 ≤
      (integerPolynomialReal baseCoefficients).eval
          (rightEndpoint : ℝ) + coefficient) :
    coefficient ∈ septicTranslationCandidates baseCoefficients
      leftEndpoint rightEndpoint firstRoot secondRoot thirdRoot fourthRoot
      fifthRoot sixthRoot := by
  have hfirstRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients firstRoot hfirstOrdered hfirstMem
  have hsecondRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients secondRoot hsecondOrdered hsecondMem
  have hthirdRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients thirdRoot hthirdOrdered hthirdMem
  have hfourthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients fourthRoot hfourthOrdered hfourthMem
  have hfifthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients fifthRoot hfifthOrdered hfifthMem
  have hsixthRange := integerPolynomial_eval_mem_rootInterval
    baseCoefficients sixthRoot hsixthOrdered hsixthMem
  have hleftRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton leftEndpoint)
    (IntervalRat.mem_singleton leftEndpoint)
  have hrightRange := integerPolynomial_eval_mem_interval
    baseCoefficients (IntervalRat.singleton rightEndpoint)
    (IntervalRat.mem_singleton rightEndpoint)
  rw [septicTranslationCandidates, integerIcc, Finset.mem_Icc]
  constructor
  · rw [septicTranslationLowerBound, max_le_iff, max_le_iff,
      max_le_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
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
          (-((integerPolynomialRootIntervalEval
            baseCoefficients fifthRoot).hi : ℝ)) ≤ coefficient := by
        rw [IntervalRat.mem_def] at hfifthRange
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
  · rw [septicTranslationUpperBound, le_min_iff, le_min_iff,
      le_min_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
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
    · rw [Int.le_floor]
      have hreal :
          (coefficient : ℝ) ≤
            -((integerPolynomialRootIntervalEval
              baseCoefficients sixthRoot).lo : ℝ) := by
        rw [IntervalRat.mem_def] at hsixthRange
        linarith
      exact_mod_cast hreal

end TraceEuclidean
