import TraceEuclidean.VoightCoefficientPruning

/-! Shared definitions for the generated degree-five final Rolle stage. -/

namespace TraceEuclidean

/-- A certified quartic derivative stage and the coefficients determining it. -/
structure DegreeFiveStageFiveEntry where
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  a1 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
  fourthRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeFiveStageFiveEntry

def derivativeCoefficients (entry : DegreeFiveStageFiveEntry) : List ℤ :=
  [entry.a1, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4, 5]

def baseCoefficients (entry : DegreeFiveStageFiveEntry) : List ℤ :=
  [0, entry.a1, entry.a2, entry.a3, entry.a4, 1]

def rootIntervals (entry : DegreeFiveStageFiveEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot, entry.fourthRoot]

def Valid (entry : DegreeFiveStageFiveEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 4
    entry.derivativeCoefficients entry.rootIntervals

def a0Candidates (entry : DegreeFiveStageFiveEntry) : Finset ℤ :=
  quinticTranslationCandidates entry.baseCoefficients
    (-10) 10 entry.firstRoot entry.secondRoot entry.thirdRoot entry.fourthRoot

end DegreeFiveStageFiveEntry

end TraceEuclidean
