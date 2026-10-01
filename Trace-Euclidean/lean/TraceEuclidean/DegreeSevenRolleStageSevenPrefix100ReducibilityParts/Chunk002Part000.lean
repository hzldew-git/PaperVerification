import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 20 through 29. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk002Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (3 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21270375 : ℤ), (-21270372 : ℤ), (-8965022 : ℤ), (-8965019 : ℤ), (-3857314 : ℤ), (-3857311 : ℤ), (-2 : ℤ), (2 : ℤ), (7392776 : ℤ), (7392779 : ℤ), (69841341 : ℤ), (69841344 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19632019 : ℤ), (-19632016 : ℤ), (-12377422 : ℤ), (-12377419 : ℤ), (-2753645 : ℤ), (-2753642 : ℤ), (-2 : ℤ), (2 : ℤ), (8135115 : ℤ), (8135118 : ℤ), (69769377 : ℤ), (69769380 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15136690 : ℤ), (-15136687 : ℤ), (-6149661 : ℤ), (-6149658 : ℤ), (3795726 : ℤ), (3795729 : ℤ), (7710838 : ℤ), (7710841 : ℤ), (69698408 : ℤ), (69698411 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (5 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18542636 : ℤ), (-18542633 : ℤ), (-12855126 : ℤ), (-12855123 : ℤ), (-4757578 : ℤ), (-4757575 : ℤ), (-2 : ℤ), (2 : ℤ), (9611393 : ℤ), (9611396 : ℤ), (69685352 : ℤ), (69685355 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-2 : ℤ), (6 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14014086 : ℤ), (-14014083 : ℤ), (-6454616 : ℤ), (-6454613 : ℤ), (-2 : ℤ), (2 : ℤ), (10786582 : ℤ), (10786585 : ℤ), (69600742 : ℤ), (69600745 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 3, -2, -9, -3, 1], [0, 1], [0, 1, 3, -2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 4, -2, -9, -3, 1], [1, 1], [0, 0, 1, 3, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 2, 5, -2, -9, -3, 1], [1, 1], [0, 0, 2, 3, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 3, 6, -2, -9, -3, 1], [0, 1], [0, 3, 6, -2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk002Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000,
    degreeSevenStageSevenScaledPrefix100Chunk002Part000,
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
