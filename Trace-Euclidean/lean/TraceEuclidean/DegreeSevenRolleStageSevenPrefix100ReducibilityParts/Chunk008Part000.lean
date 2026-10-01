import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-26524084 : ℤ), (-26524081 : ℤ), (-8555750 : ℤ), (-8555747 : ℤ), (-2 : ℤ), (2 : ℤ), (4275734 : ℤ), (4275737 : ℤ), (5738424 : ℤ), (5738427 : ℤ), (68207082 : ℤ), (68207085 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25963076 : ℤ), (-25963073 : ℤ), (-9720705 : ℤ), (-9720702 : ℤ), (-2 : ℤ), (2 : ℤ), (2794778 : ℤ), (2794781 : ℤ), (7903332 : ℤ), (7903335 : ℤ), (68127076 : ℤ), (68127079 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (5 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25021211 : ℤ), (-25021208 : ℤ), (-12106418 : ℤ), (-12106415 : ℤ), (-2 : ℤ), (2 : ℤ), (5453480 : ℤ), (5453483 : ℤ), (6755738 : ℤ), (6755741 : ℤ), (68059816 : ℤ), (68059819 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25332450 : ℤ), (-25332447 : ℤ), (-10928773 : ℤ), (-10928770 : ℤ), (-2 : ℤ), (2 : ℤ), (2202296 : ℤ), (2202299 : ℤ), (9153787 : ℤ), (9153790 : ℤ), (68046545 : ℤ), (68046548 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25882054 : ℤ), (-25882051 : ℤ), (-7394478 : ℤ), (-7394475 : ℤ), (-2642430 : ℤ), (-2642427 : ℤ), (-2 : ℤ), (2 : ℤ), (11040422 : ℤ), (11040425 : ℤ), (68019945 : ℤ), (68019948 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, -1, 4, 2, -9, -3, 1], [0, 1], [0, -1, 4, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, -1, 5, 2, -9, -3, 1], [0, 1], [0, -1, 5, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 5, 2, -9, -3, 1], [0, 1], [0, 1, 5, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000,
    degreeSevenStageSevenScaledPrefix100Chunk008Part000,
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
