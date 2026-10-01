import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 10 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part010 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (1 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-21927082 : ℤ), (-21927079 : ℤ), (-13106943 : ℤ), (-13106940 : ℤ), (-7568201 : ℤ), (-7568198 : ℤ), (4919164 : ℤ), (4919167 : ℤ), (13211282 : ℤ), (13211285 : ℤ), (67613184 : ℤ), (67613187 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-21602728 : ℤ), (-21602725 : ℤ), (-14506384 : ℤ), (-14506381 : ℤ), (-5763639 : ℤ), (-5763636 : ℤ), (3849755 : ℤ), (3849758 : ℤ), (13552934 : ℤ), (13552937 : ℤ), (67611465 : ℤ), (67611468 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21204453 : ℤ), (-21204450 : ℤ), (-15648192 : ℤ), (-15648189 : ℤ), (-4019374 : ℤ), (-4019371 : ℤ), (2550411 : ℤ), (2550414 : ℤ), (13853267 : ℤ), (13853270 : ℤ), (67609745 : ℤ), (67609748 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20665185 : ℤ), (-20665182 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-1147222 : ℤ), (-1147219 : ℤ), (-2 : ℤ), (2 : ℤ), (14123004 : ℤ), (14123007 : ℤ), (67608025 : ℤ), (67608028 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-22370299 : ℤ), (-22370296 : ℤ), (-12182250 : ℤ), (-12182247 : ℤ), (-7311388 : ℤ), (-7311385 : ℤ), (3369936 : ℤ), (3369939 : ℤ), (14037808 : ℤ), (14037811 : ℤ), (67597596 : ℤ), (67597599 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 1, 10, 2, -9, -3, 1], [-1, 1], [0, 2, 1, -9, -11, -2, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part010 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010,
    degreeSevenStageSevenScaledPrefix100Chunk008Part010,
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
