import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 5 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part005 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-21579796 : ℤ), (-21579793 : ℤ), (-12858032 : ℤ), (-12858029 : ℤ), (-4424361 : ℤ), (-4424358 : ℤ), (-2277450 : ℤ), (-2277447 : ℤ), (16914346 : ℤ), (16914349 : ℤ), (67366697 : ℤ), (67366700 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (2 : ℤ), (-7 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14450444 : ℤ), (-14450441 : ℤ), (-14130093 : ℤ), (-14130090 : ℤ), (6681877 : ℤ), (6681880 : ℤ), (14465170 : ℤ), (14465173 : ℤ), (67352111 : ℤ), (67352114 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (4 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-17672479 : ℤ), (-17672476 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-9127698 : ℤ), (-9127695 : ℤ), (3247425 : ℤ), (3247428 : ℤ), (16154852 : ℤ), (16154855 : ℤ), (67316520 : ℤ), (67316523 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (5 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19653685 : ℤ), (-19653682 : ℤ), (-13972129 : ℤ), (-13972126 : ℤ), (-9374293 : ℤ), (-9374290 : ℤ), (2211620 : ℤ), (2211623 : ℤ), (16629440 : ℤ), (16629443 : ℤ), (67300451 : ℤ), (67300454 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (13 : ℤ), (5 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-18321183 : ℤ), (-18321180 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-7124522 : ℤ), (-7124519 : ℤ), (1288444 : ℤ), (1288447 : ℤ), (16777214 : ℤ), (16777218 : ℤ), (67298668 : ℤ), (67298671 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005 :
    List PolynomialFactorCertificate :=
  [
    ⟨[-1, -3, 4, 13, 2, -9, -3, 1], [1, 1], [-1, -2, 6, 7, -5, -4, 1], 1, 6⟩,
    ⟨[0, -1, 5, 13, 2, -9, -3, 1], [0, 1], [-1, 5, 13, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005,
    degreeSevenStageSevenScaledPrefix100Chunk009Part005,
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
