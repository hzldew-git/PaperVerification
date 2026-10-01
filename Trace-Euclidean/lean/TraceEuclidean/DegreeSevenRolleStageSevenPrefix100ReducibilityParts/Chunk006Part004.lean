import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 4 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part004 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (0 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-21549896 : ℤ), (-21549893 : ℤ), (-12762799 : ℤ), (-12762796 : ℤ), (-7456896 : ℤ), (-7456893 : ℤ), (7223039 : ℤ), (7223042 : ℤ), (9455448 : ℤ), (9455451 : ℤ), (68232508 : ℤ), (68232511 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-21197027 : ℤ), (-21197024 : ℤ), (-14286756 : ℤ), (-14286753 : ℤ), (-5508208 : ℤ), (-5508205 : ℤ), (5260526 : ℤ), (5260529 : ℤ), (10641974 : ℤ), (10641977 : ℤ), (68230894 : ℤ), (68230897 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-20752211 : ℤ), (-20752208 : ℤ), (-15517854 : ℤ), (-15517851 : ℤ), (-3642954 : ℤ), (-3642951 : ℤ), (3520966 : ℤ), (3520969 : ℤ), (11304177 : ℤ), (11304180 : ℤ), (68229279 : ℤ), (68229282 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-22012758 : ℤ), (-22012755 : ℤ), (-11816503 : ℤ), (-11816500 : ℤ), (-7128538 : ℤ), (-7128535 : ℤ), (4379403 : ℤ), (4379406 : ℤ), (11502046 : ℤ), (11502049 : ℤ), (68217753 : ℤ), (68217756 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21730812 : ℤ), (-21730809 : ℤ), (-13439088 : ℤ), (-13439085 : ℤ), (-4717375 : ℤ), (-4717372 : ℤ), (2828742 : ℤ), (2828745 : ℤ), (11983801 : ℤ), (11983804 : ℤ), (68216135 : ℤ), (68216138 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 1, 8, 1, -9, -3, 1], [0, 1], [-1, 1, 8, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004,
    degreeSevenStageSevenScaledPrefix100Chunk006Part004,
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
