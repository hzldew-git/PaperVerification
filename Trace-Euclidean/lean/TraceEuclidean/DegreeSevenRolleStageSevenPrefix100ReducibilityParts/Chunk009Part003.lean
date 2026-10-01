import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 3 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part003 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (1 : ℤ), (-6 : ℤ), (16777216 : ℤ), (-17734950 : ℤ), (-17734947 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-10213489 : ℤ), (-10213486 : ℤ), (6897689 : ℤ), (6897692 : ℤ), (13519625 : ℤ), (13519628 : ℤ), (67449745 : ℤ), (67449748 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (2 : ℤ), (-5 : ℤ), (16777216 : ℤ), (-19725081 : ℤ), (-19725078 : ℤ), (-13635441 : ℤ), (-13635438 : ℤ), (-10918651 : ℤ), (-10918648 : ℤ), (5585417 : ℤ), (5585420 : ℤ), (14401257 : ℤ), (14401260 : ℤ), (67433902 : ℤ), (67433905 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (2 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-18403649 : ℤ), (-18403646 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-8619180 : ℤ), (-8619177 : ℤ), (4841160 : ℤ), (4841163 : ℤ), (14668142 : ℤ), (14668145 : ℤ), (67432148 : ℤ), (67432151 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (3 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-20000246 : ℤ), (-20000243 : ℤ), (-14567140 : ℤ), (-14567137 : ℤ), (-8677070 : ℤ), (-8677067 : ℤ), (3663884 : ℤ), (3663887 : ℤ), (15305704 : ℤ), (15305707 : ℤ), (67416272 : ℤ), (67416275 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (3 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-18936986 : ℤ), (-18936983 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6861355 : ℤ), (-6861352 : ℤ), (2796060 : ℤ), (2796063 : ℤ), (15506390 : ℤ), (15506393 : ℤ), (67414513 : ℤ), (67414516 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003 :
    List PolynomialFactorCertificate :=
  [
    ⟨[-1, -4, 2, 12, 2, -9, -3, 1], [-1, 1], [1, 5, 3, -9, -11, -2, 1], 1, 6⟩,
    ⟨[-1, -3, 3, 12, 2, -9, -3, 1], [1, 1], [-1, -2, 5, 7, -5, -4, 1], 1, 6⟩,
    ⟨[0, -2, 3, 12, 2, -9, -3, 1], [0, 1], [-2, 3, 12, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003,
    degreeSevenStageSevenScaledPrefix100Chunk009Part003,
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
