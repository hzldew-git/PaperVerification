import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 6 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part006 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (6 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-20507514 : ℤ), (-20507511 : ℤ), (-11818106 : ℤ), (-11818103 : ℤ), (-10019882 : ℤ), (-10019879 : ℤ), (1142913 : ℤ), (1142916 : ℤ), (17059642 : ℤ), (17059645 : ℤ), (67284351 : ℤ), (67284354 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (6 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19923368 : ℤ), (-19923365 : ℤ), (-14671595 : ℤ), (-14671592 : ℤ), (-6738978 : ℤ), (-6738975 : ℤ), (-2 : ℤ), (2 : ℤ), (17192782 : ℤ), (17192785 : ℤ), (67282564 : ℤ), (67282567 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (7 : ℤ), (1 : ℤ), (16777216 : ℤ), (-20723753 : ℤ), (-20723750 : ℤ), (-13352523 : ℤ), (-13352520 : ℤ), (-6003329 : ℤ), (-6003326 : ℤ), (-1622049 : ℤ), (-1622046 : ℤ), (17576628 : ℤ), (17576631 : ℤ), (67266430 : ℤ), (67266433 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (14 : ℤ), (5 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15275493 : ℤ), (-15275490 : ℤ), (-12366300 : ℤ), (-12366297 : ℤ), (3565520 : ℤ), (3565523 : ℤ), (16777214 : ℤ), (16777218 : ℤ), (67217679 : ℤ), (67217682 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (14 : ℤ), (7 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19321291 : ℤ), (-19321288 : ℤ), (-12801061 : ℤ), (-12801058 : ℤ), (-10667934 : ℤ), (-10667931 : ℤ), (1013366 : ℤ), (1013370 : ℤ), (17734951 : ℤ), (17734954 : ℤ), (67183373 : ℤ), (67183376 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 6, 13, 2, -9, -3, 1], [1, 1], [0, 0, 6, 7, -5, -4, 1], 1, 6⟩,
    ⟨[0, 1, 7, 13, 2, -9, -3, 1], [0, 1], [1, 7, 13, 2, -9, -3, 1], 1, 6⟩,
    ⟨[-2, -4, 5, 14, 2, -9, -3, 1], [1, 1], [-2, -2, 7, 7, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part006 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006,
    degreeSevenStageSevenScaledPrefix100Chunk009Part006,
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
