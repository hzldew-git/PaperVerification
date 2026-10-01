import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 30 through 39. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk003Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23133420 : ℤ), (-23133417 : ℤ), (-6074202 : ℤ), (-6074199 : ℤ), (-4951205 : ℤ), (-4951202 : ℤ), (-2 : ℤ), (2 : ℤ), (7861182 : ℤ), (7861185 : ℤ), (69439050 : ℤ), (69439053 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22142941 : ℤ), (-22142938 : ℤ), (-9764884 : ℤ), (-9764881 : ℤ), (-2937125 : ℤ), (-2937122 : ℤ), (-2 : ℤ), (2 : ℤ), (8621150 : ℤ), (8621153 : ℤ), (69365205 : ℤ), (69365208 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21124276 : ℤ), (-21124273 : ℤ), (-9857430 : ℤ), (-9857427 : ℤ), (-7201294 : ℤ), (-7201291 : ℤ), (3664022 : ℤ), (3664025 : ℤ), (8368000 : ℤ), (8368003 : ℤ), (69292382 : ℤ), (69292385 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20790447 : ℤ), (-20790444 : ℤ), (-12422950 : ℤ), (-12422947 : ℤ), (-2272856 : ℤ), (-2272853 : ℤ), (-2 : ℤ), (2 : ℤ), (9336732 : ℤ), (9336735 : ℤ), (69290927 : ℤ), (69290930 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (5 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21558435 : ℤ), (-21558432 : ℤ), (-9152421 : ℤ), (-9152418 : ℤ), (-5510412 : ℤ), (-5510409 : ℤ), (-2 : ℤ), (2 : ℤ), (10083780 : ℤ), (10083783 : ℤ), (69278894 : ℤ), (69278897 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 4, -1, -9, -3, 1], [0, 1], [0, 1, 4, -1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 5, -1, -9, -3, 1], [1, 1], [0, 0, 1, 4, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk003Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000,
    degreeSevenStageSevenScaledPrefix100Chunk003Part000,
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
