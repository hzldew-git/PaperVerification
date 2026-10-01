import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 7 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part007 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20329691 : ℤ), (-20329688 : ℤ), (-17977244 : ℤ), (-17977241 : ℤ), (-2 : ℤ), (2 : ℤ), (1227409 : ℤ), (1227412 : ℤ), (12501931 : ℤ), (12501934 : ℤ), (67718999 : ℤ), (67719002 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (0 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-22616269 : ℤ), (-22616266 : ℤ), (-12725410 : ℤ), (-12725407 : ℤ), (-6960882 : ℤ), (-6960879 : ℤ), (6009870 : ℤ), (6009873 : ℤ), (11723713 : ℤ), (11723716 : ℤ), (67710381 : ℤ), (67710384 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-22370341 : ℤ), (-22370338 : ℤ), (-13977846 : ℤ), (-13977843 : ℤ), (-5203395 : ℤ), (-5203392 : ℤ), (4713338 : ℤ), (4713341 : ℤ), (12270966 : ℤ), (12270969 : ℤ), (67708681 : ℤ), (67708684 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22089071 : ℤ), (-22089068 : ℤ), (-14971999 : ℤ), (-14971996 : ℤ), (-3452229 : ℤ), (-3452226 : ℤ), (3244194 : ℤ), (3244197 : ℤ), (12703528 : ℤ), (12703531 : ℤ), (67706981 : ℤ), (67706984 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-22985655 : ℤ), (-22985652 : ℤ), (-11973858 : ℤ), (-11973855 : ℤ), (-6547469 : ℤ), (-6547466 : ℤ), (4046877 : ℤ), (4046880 : ℤ), (12906562 : ℤ), (12906565 : ℤ), (67694947 : ℤ), (67694950 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 0, 9, 2, -9, -3, 1], [0, 1], [-2, 0, 9, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part007 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007,
    degreeSevenStageSevenScaledPrefix100Chunk008Part007,
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
