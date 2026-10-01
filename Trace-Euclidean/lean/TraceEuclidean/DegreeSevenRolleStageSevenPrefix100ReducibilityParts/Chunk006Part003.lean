import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 3 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part003 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22414540 : ℤ), (-22414537 : ℤ), (-13080134 : ℤ), (-13080131 : ℤ), (-3978468 : ℤ), (-3978465 : ℤ), (3809454 : ℤ), (3809457 : ℤ), (10495951 : ℤ), (10495954 : ℤ), (68309141 : ℤ), (68309144 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22981114 : ℤ), (-22981111 : ℤ), (-11019213 : ℤ), (-11019210 : ℤ), (-5445465 : ℤ), (-5445462 : ℤ), (2994469 : ℤ), (2994472 : ℤ), (11296630 : ℤ), (11296633 : ℤ), (68296097 : ℤ), (68296100 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22786021 : ℤ), (-22786018 : ℤ), (-12472207 : ℤ), (-12472204 : ℤ), (-1662780 : ℤ), (-1662777 : ℤ), (-2 : ℤ), (2 : ℤ), (11767919 : ℤ), (11767922 : ℤ), (68294494 : ℤ), (68294497 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23291462 : ℤ), (-23291459 : ℤ), (-10473996 : ℤ), (-10473993 : ℤ), (-3699646 : ℤ), (-3699643 : ℤ), (-2 : ℤ), (2 : ℤ), (12325080 : ℤ), (12325083 : ℤ), (68281429 : ℤ), (68281432 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (-1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19759420 : ℤ), (-19759417 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-4529457 : ℤ), (-4529454 : ℤ), (6745302 : ℤ), (6745305 : ℤ), (9218180 : ℤ), (9218183 : ℤ), (68244016 : ℤ), (68244019 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 0, 7, 1, -9, -3, 1], [0, 1], [-1, 0, 7, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 7, 1, -9, -3, 1], [1, 1], [0, 0, 1, 6, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 2, 7, 1, -9, -3, 1], [0, 1], [0, 2, 7, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003,
    degreeSevenStageSevenScaledPrefix100Chunk006Part003,
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
