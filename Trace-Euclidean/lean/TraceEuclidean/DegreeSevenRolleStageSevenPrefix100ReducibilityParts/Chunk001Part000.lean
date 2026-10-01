import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 10 through 19. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk001Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-4 : ℤ), (2 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-12115498 : ℤ), (-12115495 : ℤ), (-4513188 : ℤ), (-4513185 : ℤ), (-2 : ℤ), (2 : ℤ), (5856291 : ℤ), (5856294 : ℤ), (70691018 : ℤ), (70691021 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18316088 : ℤ), (-18316085 : ℤ), (-12296434 : ℤ), (-12296431 : ℤ), (-3446957 : ℤ), (-3446954 : ℤ), (-2 : ℤ), (2 : ℤ), (6965065 : ℤ), (6965068 : ℤ), (70235819 : ℤ), (70235822 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (4 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13046051 : ℤ), (-13046048 : ℤ), (-5767070 : ℤ), (-5767067 : ℤ), (-2 : ℤ), (2 : ℤ), (8577334 : ℤ), (8577337 : ℤ), (70154409 : ℤ), (70154412 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-3 : ℤ), (5 : ℤ), (4 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-11056366 : ℤ), (-11056363 : ℤ), (-6193519 : ℤ), (-6193516 : ℤ), (-3671572 : ℤ), (-3671569 : ℤ), (10780304 : ℤ), (10780307 : ℤ), (70059774 : ℤ), (70059777 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 2, -4, -9, -3, 1], [0, 1], [0, 1, 2, -4, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 3, -3, -9, -3, 1], [1, 1], [0, 0, 1, 2, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 2, 4, -3, -9, -3, 1], [0, 1], [0, 2, 4, -3, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk001Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000,
    degreeSevenStageSevenScaledPrefix100Chunk001Part000,
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
