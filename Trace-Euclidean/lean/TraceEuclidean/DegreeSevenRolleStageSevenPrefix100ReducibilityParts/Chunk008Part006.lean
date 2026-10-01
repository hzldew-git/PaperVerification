import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 6 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part006 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24092396 : ℤ), (-24092393 : ℤ), (-10795239 : ℤ), (-10795236 : ℤ), (-3200064 : ℤ), (-3200061 : ℤ), (-2 : ℤ), (2 : ℤ), (13468277 : ℤ), (13468280 : ℤ), (67760827 : ℤ), (67760830 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (-2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19793314 : ℤ), (-19793311 : ℤ), (-18268958 : ℤ), (-18268955 : ℤ), (-3682914 : ℤ), (-3682911 : ℤ), (6871735 : ℤ), (6871738 : ℤ), (10278768 : ℤ), (10278771 : ℤ), (67736088 : ℤ), (67736091 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (-1 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-21893721 : ℤ), (-21893718 : ℤ), (-14743196 : ℤ), (-14743193 : ℤ), (-5735259 : ℤ), (-5735256 : ℤ), (7196260 : ℤ), (7196263 : ℤ), (10593227 : ℤ), (10593230 : ℤ), (67724092 : ℤ), (67724095 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (-1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-21533213 : ℤ), (-21533210 : ℤ), (-15768779 : ℤ), (-15768776 : ℤ), (-4329820 : ℤ), (-4329817 : ℤ), (5577841 : ℤ), (5577844 : ℤ), (11472980 : ℤ), (11472983 : ℤ), (67722395 : ℤ), (67722398 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21066450 : ℤ), (-21066447 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-2771543 : ℤ), (-2771540 : ℤ), (3985257 : ℤ), (3985260 : ℤ), (12050660 : ℤ), (12050663 : ℤ), (67720697 : ℤ), (67720700 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 2, 8, 2, -9, -3, 1], [0, 1], [0, 2, 8, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part006 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006,
    degreeSevenStageSevenScaledPrefix100Chunk008Part006,
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
