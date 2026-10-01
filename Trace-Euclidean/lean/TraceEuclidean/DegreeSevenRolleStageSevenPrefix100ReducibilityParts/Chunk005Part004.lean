import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 4 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part004 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18094472 : ℤ), (-18094469 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-2955176 : ℤ), (-2955173 : ℤ), (-2 : ℤ), (2 : ℤ), (12336338 : ℤ), (12336341 : ℤ), (68631932 : ℤ), (68631935 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20265005 : ℤ), (-20265002 : ℤ), (-13160543 : ℤ), (-13160540 : ℤ), (-4860629 : ℤ), (-4860626 : ℤ), (-2 : ℤ), (2 : ℤ), (12808381 : ℤ), (12808384 : ℤ), (68619201 : ℤ), (68619204 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (9 : ℤ), (2 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15800211 : ℤ), (-15800208 : ℤ), (-9369630 : ℤ), (-9369627 : ℤ), (4774554 : ℤ), (4774557 : ℤ), (11755586 : ℤ), (11755589 : ℤ), (68558322 : ℤ), (68558325 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (9 : ℤ), (3 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-18903241 : ℤ), (-18903238 : ℤ), (-12382728 : ℤ), (-12382725 : ℤ), (-9972383 : ℤ), (-9972380 : ℤ), (3129048 : ℤ), (3129051 : ℤ), (12726776 : ℤ), (12726779 : ℤ), (68543932 : ℤ), (68543935 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (9 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19135959 : ℤ), (-19135956 : ℤ), (-13883109 : ℤ), (-13883106 : ℤ), (-6083549 : ℤ), (-6083546 : ℤ), (-2 : ℤ), (2 : ℤ), (13716076 : ℤ), (13716079 : ℤ), (68527946 : ℤ), (68527949 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 3, 8, 0, -9, -3, 1], [-1, 1], [0, 0, -3, -11, -11, -2, 1], 1, 6⟩,
    ⟨[0, 0, 4, 9, 0, -9, -3, 1], [1, 1], [0, 0, 4, 5, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004,
    degreeSevenStageSevenScaledPrefix100Chunk005Part004,
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
