import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 20 through 29. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk002Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (7 : ℤ), (5 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12352659 : ℤ), (-12352656 : ℤ), (-7309361 : ℤ), (-7309358 : ℤ), (-2420904 : ℤ), (-2420901 : ℤ), (12499298 : ℤ), (12499301 : ℤ), (69502246 : ℤ), (69502249 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001 :
    List PolynomialFactorCertificate :=
  [

  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk002Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001,
    degreeSevenStageSevenScaledPrefix100Chunk002Part001,
    degreeSevenStageSevenFinalCoefficients,
    DegreeSevenStageSevenScaledEntry.scaledA0Candidates,
    DegreeSevenStageSevenScaledEntry.scaledA0LowerBound,
    DegreeSevenStageSevenScaledEntry.scaledA0UpperBound,
    DegreeSevenStageSevenScaledEntry.scaledRootValueRange,
    DegreeSevenStageSevenScaledEntry.scaledEndpointValueRange,
    DegreeSevenStageSevenScaledEntry.scaledBaseCoefficients,
    scaledIntegerPolynomialIntervalEval, integerMin4,
    integerMax4, integerIcc, min_def, max_def, Int.toNat]

end

end TraceEuclidean
