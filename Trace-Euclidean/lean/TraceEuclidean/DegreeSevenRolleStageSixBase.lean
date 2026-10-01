import TraceEuclidean.VoightHigherCoefficientPruning

/-!
# Shared definitions for the sixth Rolle stage in degree seven

The finite data layer will attach five exact rational root intervals to each
separable quintic reached by the fifth stage.  This file fixes the proof-facing
interface independently of the generated data layout.
-/

namespace TraceEuclidean

/-- A certified quintic second-derivative stage and the top coefficients
determining it. -/
structure DegreeSevenStageSixEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
  fourthRoot : RationalRootInterval
  fifthRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageSixEntry

/-- The normalized second derivative whose five roots control the next
translation. -/
def derivativeCoefficients (entry : DegreeSevenStageSixEntry) : List ℤ :=
  [entry.a2, 3 * entry.a3, 6 * entry.a4, 10 * entry.a5,
    15 * entry.a6, 21]

/-- The normalized first derivative with zero constant coefficient. -/
def baseCoefficients (entry : DegreeSevenStageSixEntry) : List ℤ :=
  [0, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4,
    5 * entry.a5, 6 * entry.a6, 7]

def rootIntervals (entry : DegreeSevenStageSixEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot,
    entry.fourthRoot, entry.fifthRoot]

/-- Exact certification that the stored intervals isolate all five real roots
of the quintic second-derivative stage. -/
def Valid (entry : DegreeSevenStageSixEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 5
    entry.derivativeCoefficients entry.rootIntervals

def leftEndpoint (entry : DegreeSevenStageSixEntry) : ℚ :=
  (-(entry.a6 : ℚ) - 38) / 7

def rightEndpoint (entry : DegreeSevenStageSixEntry) : ℚ :=
  (-(entry.a6 : ℚ) + 38) / 7

/-- Exact integer translations allowed for the coefficient `a1`. -/
def a1Candidates (entry : DegreeSevenStageSixEntry) : Finset ℤ :=
  sexticTranslationCandidates entry.baseCoefficients
    entry.leftEndpoint entry.rightEndpoint entry.firstRoot entry.secondRoot
      entry.thirdRoot entry.fourthRoot entry.fifthRoot

end DegreeSevenStageSixEntry

end TraceEuclidean
