import TraceEuclidean.VoightHigherCoefficientPruning

/-! Shared definitions for the generated degree-seven fourth Rolle stage. -/

namespace TraceEuclidean

/-- A certified cubic derivative stage and the top coefficients determining
it. -/
structure DegreeSevenStageFourEntry where
  a6 : ℤ
  a5 : ℤ
  a4 : ℤ
  firstRoot : RationalRootInterval
  secondRoot : RationalRootInterval
  thirdRoot : RationalRootInterval
deriving DecidableEq, Repr

namespace DegreeSevenStageFourEntry

def derivativeCoefficients (entry : DegreeSevenStageFourEntry) : List ℤ :=
  [entry.a4, 5 * entry.a5, 15 * entry.a6, 35]

def baseCoefficients (entry : DegreeSevenStageFourEntry) : List ℤ :=
  [0, 4 * entry.a4, 10 * entry.a5, 20 * entry.a6, 35]

def rootIntervals (entry : DegreeSevenStageFourEntry) :
    List RationalRootInterval :=
  [entry.firstRoot, entry.secondRoot, entry.thirdRoot]

def Valid (entry : DegreeSevenStageFourEntry) : Prop :=
  GeneralRationalRootIntervalCertificate.Valid 3
    entry.derivativeCoefficients entry.rootIntervals

def a3Candidates (entry : DegreeSevenStageFourEntry) : Finset ℤ :=
  quarticTranslationCandidates entry.baseCoefficients
    (-16) 16 entry.firstRoot entry.secondRoot entry.thirdRoot

end DegreeSevenStageFourEntry

end TraceEuclidean
