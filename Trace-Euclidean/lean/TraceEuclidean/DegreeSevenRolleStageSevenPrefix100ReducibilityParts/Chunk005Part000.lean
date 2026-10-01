import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21797180 : ℤ), (-21797177 : ℤ), (-13941197 : ℤ), (-13941194 : ℤ), (-2 : ℤ), (2 : ℤ), (2390369 : ℤ), (2390372 : ℤ), (7588204 : ℤ), (7588207 : ℤ), (68901209 : ℤ), (68901212 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (5 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22657836 : ℤ), (-22657833 : ℤ), (-10753435 : ℤ), (-10753432 : ℤ), (-4917795 : ℤ), (-4917792 : ℤ), (5304982 : ℤ), (5304985 : ℤ), (7275170 : ℤ), (7275173 : ℤ), (68890317 : ℤ), (68890320 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22977141 : ℤ), (-22977138 : ℤ), (-10257127 : ℤ), (-10257124 : ℤ), (-2370464 : ℤ), (-2370461 : ℤ), (-2 : ℤ), (2 : ℤ), (9869751 : ℤ), (9869754 : ℤ), (68876386 : ℤ), (68876389 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (6 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19549870 : ℤ), (-19549867 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-2 : ℤ), (2 : ℤ), (1930885 : ℤ), (1930888 : ℤ), (8712986 : ℤ), (8712989 : ℤ), (68824621 : ℤ), (68824624 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (6 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21370762 : ℤ), (-21370759 : ℤ), (-13180755 : ℤ), (-13180752 : ℤ), (-4274362 : ℤ), (-4274359 : ℤ), (4385276 : ℤ), (4385279 : ℤ), (8768356 : ℤ), (8768359 : ℤ), (68813652 : ℤ), (68813655 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 5, 0, -9, -3, 1], [0, 1], [0, 1, 5, 0, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000,
    degreeSevenStageSevenScaledPrefix100Chunk005Part000,
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
