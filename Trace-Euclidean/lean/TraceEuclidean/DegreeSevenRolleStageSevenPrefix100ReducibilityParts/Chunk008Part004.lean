import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 4 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part004 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24871866 : ℤ), (-24871863 : ℤ), (-8741669 : ℤ), (-8741666 : ℤ), (-3990943 : ℤ), (-3990940 : ℤ), (-2 : ℤ), (2 : ℤ), (12902573 : ℤ), (12902576 : ℤ), (67843311 : ℤ), (67843314 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (-2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22067369 : ℤ), (-22067366 : ℤ), (-15956220 : ℤ), (-15956217 : ℤ), (-2362190 : ℤ), (-2362187 : ℤ), (5569605 : ℤ), (5569608 : ℤ), (10140591 : ℤ), (10140594 : ℤ), (67816986 : ℤ), (67816989 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21698138 : ℤ), (-21698135 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-2 : ℤ), (2 : ℤ), (2795533 : ℤ), (2795536 : ℤ), (11005921 : ℤ), (11005924 : ℤ), (67815306 : ℤ), (67815309 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (-1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-23017207 : ℤ), (-23017204 : ℤ), (-13586674 : ℤ), (-13586671 : ℤ), (-4658690 : ℤ), (-4658687 : ℤ), (6206403 : ℤ), (6206406 : ℤ), (10392489 : ℤ), (10392492 : ℤ), (67805082 : ℤ), (67805085 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22798637 : ℤ), (-22798634 : ℤ), (-14483831 : ℤ), (-14483828 : ℤ), (-2930143 : ℤ), (-2930140 : ℤ), (4326501 : ℤ), (4326504 : ℤ), (11224113 : ℤ), (11224116 : ℤ), (67803400 : ℤ), (67803403 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 2, 7, 2, -9, -3, 1], [-1, 1], [0, 0, -2, -9, -11, -2, 1], 1, 6⟩,
    ⟨[0, -1, -1, 8, 2, -9, -3, 1], [0, 1], [-1, -1, 8, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004,
    degreeSevenStageSevenScaledPrefix100Chunk008Part004,
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
