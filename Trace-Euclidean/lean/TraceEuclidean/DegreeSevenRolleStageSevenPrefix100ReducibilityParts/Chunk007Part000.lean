import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (0 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-19904757 : ℤ), (-19904754 : ℤ), (-14655433 : ℤ), (-14655430 : ℤ), (-8176539 : ℤ), (-8176536 : ℤ), (8478574 : ℤ), (8478577 : ℤ), (9245778 : ℤ), (9245781 : ℤ), (68153781 : ℤ), (68153784 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (0 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-18831167 : ℤ), (-18831164 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6519668 : ℤ), (-6519665 : ℤ), (6285493 : ℤ), (6285496 : ℤ), (10831811 : ℤ), (10831814 : ℤ), (68152152 : ℤ), (68152155 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (1 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-20700267 : ℤ), (-20700264 : ℤ), (-13278899 : ℤ), (-13278896 : ℤ), (-8115263 : ℤ), (-8115260 : ℤ), (5355184 : ℤ), (5355187 : ℤ), (11741737 : ℤ), (11741740 : ℤ), (68138911 : ℤ), (68138914 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20166543 : ℤ), (-20166540 : ℤ), (-15064945 : ℤ), (-15064942 : ℤ), (-6110910 : ℤ), (-6110907 : ℤ), (4119449 : ℤ), (4119452 : ℤ), (12227073 : ℤ), (12227076 : ℤ), (68137280 : ℤ), (68137283 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19273800 : ℤ), (-19273797 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-4257445 : ℤ), (-4257442 : ℤ), (2690423 : ℤ), (2690426 : ℤ), (12623794 : ℤ), (12623797 : ℤ), (68135648 : ℤ), (68135651 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 1, 9, 1, -9, -3, 1], [0, 1], [-2, 1, 9, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000,
    degreeSevenStageSevenScaledPrefix100Chunk007Part000,
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
