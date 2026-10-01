import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 3 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part003 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21864020 : ℤ), (-21864017 : ℤ), (-9436233 : ℤ), (-9436230 : ℤ), (-6542447 : ℤ), (-6542444 : ℤ), (-2 : ℤ), (2 : ℤ), (12286988 : ℤ), (12286991 : ℤ), (68697116 : ℤ), (68697119 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (1 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-19187198 : ℤ), (-19187195 : ℤ), (-13616187 : ℤ), (-13616184 : ℤ), (-8776028 : ℤ), (-8776025 : ℤ), (6073090 : ℤ), (6073093 : ℤ), (9998426 : ℤ), (9998429 : ℤ), (68649302 : ℤ), (68649305 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-17515401 : ℤ), (-17515398 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6510815 : ℤ), (-6510812 : ℤ), (4488137 : ℤ), (4488140 : ℤ), (10808950 : ℤ), (10808953 : ℤ), (68647750 : ℤ), (68647753 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20061674 : ℤ), (-20061671 : ℤ), (-11764689 : ℤ), (-11764686 : ℤ), (-8996781 : ℤ), (-8996778 : ℤ), (3787975 : ℤ), (3787978 : ℤ), (11541531 : ℤ), (11541534 : ℤ), (68635041 : ℤ), (68635044 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (8 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19433271 : ℤ), (-19433268 : ℤ), (-14417568 : ℤ), (-14417565 : ℤ), (-5942308 : ℤ), (-5942305 : ℤ), (2328691 : ℤ), (2328694 : ℤ), (11972373 : ℤ), (11972376 : ℤ), (68633487 : ℤ), (68633490 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 1, 8, 0, -9, -3, 1], [0, 1], [-2, 1, 8, 0, -9, -3, 1], 1, 6⟩,
    ⟨[0, -1, 2, 8, 0, -9, -3, 1], [0, 1], [-1, 2, 8, 0, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003,
    degreeSevenStageSevenScaledPrefix100Chunk005Part003,
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
