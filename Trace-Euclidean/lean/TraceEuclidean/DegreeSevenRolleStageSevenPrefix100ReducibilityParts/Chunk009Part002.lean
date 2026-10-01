import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 2 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part002 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20869109 : ℤ), (-20869106 : ℤ), (-15499109 : ℤ), (-15499106 : ℤ), (-3388337 : ℤ), (-3388334 : ℤ), (-2 : ℤ), (2 : ℤ), (15402036 : ℤ), (15402039 : ℤ), (67495924 : ℤ), (67495927 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (4 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22123904 : ℤ), (-22123901 : ℤ), (-11381503 : ℤ), (-11381500 : ℤ), (-7917883 : ℤ), (-7917880 : ℤ), (1521822 : ℤ), (1521825 : ℤ), (15559237 : ℤ), (15559240 : ℤ), (67483635 : ℤ), (67483638 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21843812 : ℤ), (-21843809 : ℤ), (-13316764 : ℤ), (-13316761 : ℤ), (-4917453 : ℤ), (-4917450 : ℤ), (-2 : ℤ), (2 : ℤ), (15737546 : ℤ), (15737549 : ℤ), (67481889 : ℤ), (67481892 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (5 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22524091 : ℤ), (-22524087 : ℤ), (-10297779 : ℤ), (-10297776 : ℤ), (-7558460 : ℤ), (-7558457 : ℤ), (-2 : ℤ), (2 : ℤ), (16053903 : ℤ), (16053906 : ℤ), (67467832 : ℤ), (67467835 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-22878869 : ℤ), (-22878866 : ℤ), (-9425734 : ℤ), (-9425731 : ℤ), (-6448146 : ℤ), (-6448143 : ℤ), (-2058460 : ℤ), (-2058457 : ℤ), (16500612 : ℤ), (16500615 : ℤ), (67451999 : ℤ), (67452002 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 4, 11, 2, -9, -3, 1], [1, 1], [0, 0, 4, 7, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002,
    degreeSevenStageSevenScaledPrefix100Chunk009Part002,
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
