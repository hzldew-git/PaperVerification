import TraceEuclidean.VoightCoefficientPruning

/-! Shared definitions for the generated degree-five fourth Rolle stage. -/

namespace TraceEuclidean

/-- A certified cubic derivative stage and the top coefficients determining
it. -/
structure DegreeFiveStageFourEntry where
  a4 : ℤ
  a3 : ℤ
  a2 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeFiveStageFourEntry

def derivativeCoefficients (entry : DegreeFiveStageFourEntry) : List ℤ :=
  [entry.a2, 3 * entry.a3, 6 * entry.a4, 10]

def baseCoefficients (entry : DegreeFiveStageFourEntry) : List ℤ :=
  [0, 2 * entry.a2, 3 * entry.a3, 4 * entry.a4, 5]

def rootIntervals (entry : DegreeFiveStageFourEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot]

def Valid (entry : DegreeFiveStageFourEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 3
    entry.derivativeCoefficients entry.rootIntervals

def a1Candidates (entry : DegreeFiveStageFourEntry) : Finset ℤ :=
  quarticTranslationCandidates entry.baseCoefficients
    (-10) 10 entry.firstRoot entry.secondRoot entry.thirdRoot

end DegreeFiveStageFourEntry

end TraceEuclidean
