import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 2 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part002 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20941286 : ℤ), (-20941283 : ℤ), (-11538911 : ℤ), (-11538908 : ℤ), (-7918565 : ℤ), (-7918562 : ℤ), (4874351 : ℤ), (4874354 : ℤ), (9940363 : ℤ), (9940366 : ℤ), (68725451 : ℤ), (68725454 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-20535213 : ℤ), (-20535210 : ℤ), (-13655104 : ℤ), (-13655101 : ℤ), (-5098585 : ℤ), (-5098582 : ℤ), (3039787 : ℤ), (3039790 : ℤ), (10666607 : ℤ), (10666610 : ℤ), (68723912 : ℤ), (68723915 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19997243 : ℤ), (-19997240 : ℤ), (-15149421 : ℤ), (-15149418 : ℤ), (-1629439 : ℤ), (-1629436 : ℤ), (-2 : ℤ), (2 : ℤ), (11195135 : ℤ), (11195138 : ℤ), (68722373 : ℤ), (68722376 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21438673 : ℤ), (-21438670 : ℤ), (-10354401 : ℤ), (-10354398 : ℤ), (-7563981 : ℤ), (-7563978 : ℤ), (2431734 : ℤ), (2431737 : ℤ), (11355430 : ℤ), (11355433 : ℤ), (68711295 : ℤ), (68711298 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21121035 : ℤ), (-21121032 : ℤ), (-12733691 : ℤ), (-12733688 : ℤ), (-3490227 : ℤ), (-3490224 : ℤ), (-2 : ℤ), (2 : ℤ), (11776605 : ℤ), (11776608 : ℤ), (68709753 : ℤ), (68709756 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 1, 7, 0, -9, -3, 1], [0, 1], [-1, 1, 7, 0, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 2, 7, 0, -9, -3, 1], [1, 1], [0, 0, 2, 5, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002,
    degreeSevenStageSevenScaledPrefix100Chunk005Part002,
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
