import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 5 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part005 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (12 : ℤ), (5 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15687083 : ℤ), (-15687080 : ℤ), (-10099651 : ℤ), (-10099648 : ℤ), (2264724 : ℤ), (2264727 : ℤ), (15602463 : ℤ), (15602466 : ℤ), (67838167 : ℤ), (67838170 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (12 : ℤ), (7 : ℤ), (1 : ℤ), (16777216 : ℤ), (-19197345 : ℤ), (-19197342 : ℤ), (-13692251 : ℤ), (-13692248 : ℤ), (-6853788 : ℤ), (-6853785 : ℤ), (-1566764 : ℤ), (-1566761 : ℤ), (16645821 : ℤ), (16645824 : ℤ), (67805730 : ℤ), (67805733 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (13 : ℤ), (7 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13662509 : ℤ), (-13662506 : ℤ), (-11945812 : ℤ), (-11945809 : ℤ), (1023955 : ℤ), (1023958 : ℤ), (16777214 : ℤ), (16777218 : ℤ), (67725773 : ℤ), (67725776 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (13 : ℤ), (8 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15808429 : ℤ), (-15808426 : ℤ), (-7985281 : ℤ), (-7985278 : ℤ), (-1285032 : ℤ), (-1285029 : ℤ), (17288842 : ℤ), (17288845 : ℤ), (67708521 : ℤ), (67708524 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (13 : ℤ), (9 : ℤ), (2 : ℤ), (16777216 : ℤ), (-18910605 : ℤ), (-18910602 : ℤ), (-12709876 : ℤ), (-12709873 : ℤ), (-7685085 : ℤ), (-7685082 : ℤ), (-2888385 : ℤ), (-2888382 : ℤ), (17642403 : ℤ), (17642406 : ℤ), (67692952 : ℤ), (67692955 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005 :
    List PolynomialFactorCertificate :=
  [
    ⟨[-1, -2, 5, 12, 1, -9, -3, 1], [1, 1], [-1, -1, 6, 6, -5, -4, 1], 1, 6⟩,
    ⟨[0, 1, 7, 12, 1, -9, -3, 1], [0, 1], [1, 7, 12, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 1, 8, 13, 1, -9, -3, 1], [0, 1], [1, 8, 13, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005,
    degreeSevenStageSevenScaledPrefix100Chunk007Part005,
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
