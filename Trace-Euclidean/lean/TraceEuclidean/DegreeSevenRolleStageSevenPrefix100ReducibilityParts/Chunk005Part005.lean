import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 5 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part005 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (10 : ℤ), (4 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14360658 : ℤ), (-14360655 : ℤ), (-10557829 : ℤ), (-10557826 : ℤ), (2667623 : ℤ), (2667626 : ℤ), (13717375 : ℤ), (13717378 : ℤ), (68452111 : ℤ), (68452114 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (10 : ℤ), (5 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15895283 : ℤ), (-15895280 : ℤ), (-7157938 : ℤ), (-7157935 : ℤ), (-2 : ℤ), (2 : ℤ), (14535868 : ℤ), (14535871 : ℤ), (68435976 : ℤ), (68435979 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (10 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-18861067 : ℤ), (-18861064 : ℤ), (-13113791 : ℤ), (-13113788 : ℤ), (-6389318 : ℤ), (-6389315 : ℤ), (-1958628 : ℤ), (-1958625 : ℤ), (15042805 : ℤ), (15042808 : ℤ), (68421403 : ℤ), (68421406 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (11 : ℤ), (7 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14756506 : ℤ), (-14756503 : ℤ), (-7875654 : ℤ), (-7875651 : ℤ), (-1519107 : ℤ), (-1519104 : ℤ), (15741321 : ℤ), (15741324 : ℤ), (68328567 : ℤ), (68328570 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (11 : ℤ), (8 : ℤ), (2 : ℤ), (16777216 : ℤ), (-18613534 : ℤ), (-18613531 : ℤ), (-11825895 : ℤ), (-11825892 : ℤ), (-7289180 : ℤ), (-7289177 : ℤ), (-3598376 : ℤ), (-3598373 : ℤ), (16154554 : ℤ), (16154557 : ℤ), (68313833 : ℤ), (68313836 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005 :
    List PolynomialFactorCertificate :=
  [
    ⟨[-1, -2, 4, 10, 0, -9, -3, 1], [-1, 1], [1, 3, -1, -11, -11, -2, 1], 1, 6⟩,
    ⟨[0, 0, 5, 10, 0, -9, -3, 1], [0, 1], [0, 5, 10, 0, -9, -3, 1], 1, 6⟩,
    ⟨[0, 1, 7, 11, 0, -9, -3, 1], [0, 1], [1, 7, 11, 0, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005,
    degreeSevenStageSevenScaledPrefix100Chunk005Part005,
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
