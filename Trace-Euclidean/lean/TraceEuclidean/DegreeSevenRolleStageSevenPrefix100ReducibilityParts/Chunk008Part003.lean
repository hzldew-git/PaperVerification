import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 3 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part003 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23722548 : ℤ), (-23722545 : ℤ), (-13611439 : ℤ), (-13611436 : ℤ), (-2 : ℤ), (2 : ℤ), (1572354 : ℤ), (1572357 : ℤ), (11019163 : ℤ), (11019166 : ℤ), (67883875 : ℤ), (67883878 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-24419748 : ℤ), (-24419745 : ℤ), (-9242504 : ℤ), (-9242501 : ℤ), (-7121519 : ℤ), (-7121516 : ℤ), (5574639 : ℤ), (5574642 : ℤ), (10476821 : ℤ), (10476824 : ℤ), (67873713 : ℤ), (67873716 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24290903 : ℤ), (-24290900 : ℤ), (-11261651 : ℤ), (-11261648 : ℤ), (-4115163 : ℤ), (-4115160 : ℤ), (3715839 : ℤ), (3715842 : ℤ), (11221238 : ℤ), (11221241 : ℤ), (67872044 : ℤ), (67872047 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24652459 : ℤ), (-24652456 : ℤ), (-8911004 : ℤ), (-8911001 : ℤ), (-6056747 : ℤ), (-6056744 : ℤ), (2952603 : ℤ), (2952606 : ℤ), (11950485 : ℤ), (11950488 : ℤ), (67858525 : ℤ), (67858528 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24533333 : ℤ), (-24533330 : ℤ), (-10853336 : ℤ), (-10853333 : ℤ), (-1699163 : ℤ), (-1699160 : ℤ), (-2 : ℤ), (2 : ℤ), (12370384 : ℤ), (12370387 : ℤ), (67856853 : ℤ), (67856856 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, -1, 7, 2, -9, -3, 1], [0, 1], [0, -1, 7, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, -1, 0, 7, 2, -9, -3, 1], [0, 1], [-1, 0, 7, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 7, 2, -9, -3, 1], [0, 1], [0, 1, 7, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003,
    degreeSevenStageSevenScaledPrefix100Chunk008Part003,
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
