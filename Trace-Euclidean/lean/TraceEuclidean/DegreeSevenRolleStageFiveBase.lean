import TraceEuclidean.VoightCoefficientPruning

/-!
# Shared definitions for the fifth Rolle stage in degree seven

The finite data layer will attach four exact rational root intervals to each
separable quartic reached by the preceding stage.  This file fixes the small
proof-facing interface independently of the eventual generated data layout.
-/

namespace TraceEuclidean

/-- A certified quartic derivative stage and the top coefficients determining
it. -/
structure DegreeSevenStageFiveEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
  fourthRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageFiveEntry

/-- The normalized third derivative whose four roots control the next
translation. -/
def derivativeCoefficients (entry : DegreeSevenStageFiveEntry) : List ℤ :=
  [entry.a3, 4 * entry.a4, 10 * entry.a5, 20 * entry.a6, 35]

/-- The normalized second derivative with zero constant coefficient. -/
def baseCoefficients (entry : DegreeSevenStageFiveEntry) : List ℤ :=
  [0, 3 * entry.a3, 6 * entry.a4, 10 * entry.a5,
    15 * entry.a6, 21]

def rootIntervals (entry : DegreeSevenStageFiveEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot, entry.fourthRoot]

/-- Exact certification that the stored intervals isolate all four real roots
of the quartic derivative stage. -/
def Valid (entry : DegreeSevenStageFiveEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 4
    entry.derivativeCoefficients entry.rootIntervals

/-- Voight's left Lagrange endpoint from the two top nonleading
coefficients. -/
def leftEndpoint (entry : DegreeSevenStageFiveEntry) : ℚ :=
  (-(entry.a6 : ℚ) - 38) / 7

/-- Voight's right Lagrange endpoint from the two top nonleading
coefficients. -/
def rightEndpoint (entry : DegreeSevenStageFiveEntry) : ℚ :=
  (-(entry.a6 : ℚ) + 38) / 7

/-- Exact integer translations allowed for the coefficient `a2`. -/
def a2Candidates (entry : DegreeSevenStageFiveEntry) : Finset ℤ :=
  quinticTranslationCandidates entry.baseCoefficients
    entry.leftEndpoint entry.rightEndpoint entry.firstRoot entry.secondRoot
      entry.thirdRoot entry.fourthRoot

end DegreeSevenStageFiveEntry

end TraceEuclidean
