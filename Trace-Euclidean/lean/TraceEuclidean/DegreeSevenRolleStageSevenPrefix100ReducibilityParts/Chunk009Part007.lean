import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 7 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part007 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (14 : ℤ), (7 : ℤ), (0 : ℤ), (16777216 : ℤ), (-17616388 : ℤ), (-17616385 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-7499506 : ℤ), (-7499503 : ℤ), (-2 : ℤ), (2 : ℤ), (17852951 : ℤ), (17852954 : ℤ), (67181566 : ℤ), (67181569 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (14 : ℤ), (8 : ℤ), (1 : ℤ), (16777216 : ℤ), (-19585568 : ℤ), (-19585565 : ℤ), (-14183136 : ℤ), (-14183133 : ℤ), (-7147481 : ℤ), (-7147478 : ℤ), (-1312302 : ℤ), (-1312299 : ℤ), (18204629 : ℤ), (18204632 : ℤ), (67165262 : ℤ), (67165265 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (14 : ℤ), (9 : ℤ), (2 : ℤ), (16777216 : ℤ), (-20436167 : ℤ), (-20436164 : ℤ), (-12663041 : ℤ), (-12663038 : ℤ), (-6307233 : ℤ), (-6307230 : ℤ), (-3136429 : ℤ), (-3136426 : ℤ), (18535347 : ℤ), (18535350 : ℤ), (67148927 : ℤ), (67148930 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (15 : ℤ), (8 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15535853 : ℤ), (-15535850 : ℤ), (-10908779 : ℤ), (-10908776 : ℤ), (909106 : ℤ), (909109 : ℤ), (18372669 : ℤ), (18372672 : ℤ), (67081478 : ℤ), (67081481 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (15 : ℤ), (10 : ℤ), (2 : ℤ), (16777216 : ℤ), (-19263039 : ℤ), (-19263036 : ℤ), (-13439721 : ℤ), (-13439718 : ℤ), (-7874608 : ℤ), (-7874605 : ℤ), (-2439163 : ℤ), (-2439160 : ℤ), (19111274 : ℤ), (19111277 : ℤ), (67046661 : ℤ), (67046664 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 7, 14, 2, -9, -3, 1], [0, 1], [0, 7, 14, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 1, 8, 14, 2, -9, -3, 1], [0, 1], [1, 8, 14, 2, -9, -3, 1], 1, 6⟩,
    ⟨[-1, -1, 8, 15, 2, -9, -3, 1], [1, 1], [-1, 0, 8, 7, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part007 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007,
    degreeSevenStageSevenScaledPrefix100Chunk009Part007,
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
