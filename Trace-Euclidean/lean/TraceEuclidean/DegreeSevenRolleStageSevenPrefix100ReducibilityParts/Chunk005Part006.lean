import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 6 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part006 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (12 : ℤ), (9 : ℤ), (2 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12886266 : ℤ), (-12886263 : ℤ), (-9474705 : ℤ), (-9474702 : ℤ), (-2717732 : ℤ), (-2717729 : ℤ), (16777214 : ℤ), (16777218 : ℤ), (68220110 : ℤ), (68220113 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006 :
    List PolynomialFactorCertificate :=
  [

  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part006 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006,
    degreeSevenStageSevenScaledPrefix100Chunk005Part006,
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
