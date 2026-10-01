import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 6 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part006 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (14 : ℤ), (10 : ℤ), (2 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14454125 : ℤ), (-14454122 : ℤ), (-9108542 : ℤ), (-9108539 : ℤ), (-2341233 : ℤ), (-2341230 : ℤ), (18227772 : ℤ), (18227775 : ℤ), (67594748 : ℤ), (67594751 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 2, 10, 14, 1, -9, -3, 1], [0, 1], [2, 10, 14, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part006 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006,
    degreeSevenStageSevenScaledPrefix100Chunk007Part006,
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
