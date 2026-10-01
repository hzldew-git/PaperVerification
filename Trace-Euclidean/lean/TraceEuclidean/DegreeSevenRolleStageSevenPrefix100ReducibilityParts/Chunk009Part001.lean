import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (2 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-21097541 : ℤ), (-21097538 : ℤ), (-13670770 : ℤ), (-13670767 : ℤ), (-8149633 : ℤ), (-8149630 : ℤ), (4197990 : ℤ), (4197993 : ℤ), (14346203 : ℤ), (14346206 : ℤ), (67515154 : ℤ), (67515157 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20616342 : ℤ), (-20616339 : ℤ), (-15278415 : ℤ), (-15278412 : ℤ), (-6322072 : ℤ), (-6322069 : ℤ), (3246438 : ℤ), (3246441 : ℤ), (14598379 : ℤ), (14598382 : ℤ), (67513415 : ℤ), (67513418 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19884878 : ℤ), (-19884875 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-4607833 : ℤ), (-4607830 : ℤ), (2070007 : ℤ), (2070010 : ℤ), (14829650 : ℤ), (14829653 : ℤ), (67511676 : ℤ), (67511679 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (3 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-21659964 : ℤ), (-21659961 : ℤ), (-12506753 : ℤ), (-12506750 : ℤ), (-8069803 : ℤ), (-8069800 : ℤ), (2878731 : ℤ), (2878734 : ℤ), (14999783 : ℤ), (14999786 : ℤ), (67499409 : ℤ), (67499412 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (3 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21309497 : ℤ), (-21309494 : ℤ), (-14213508 : ℤ), (-14213505 : ℤ), (-5805783 : ℤ), (-5805780 : ℤ), (1764972 : ℤ), (1764975 : ℤ), (15207553 : ℤ), (15207556 : ℤ), (67497666 : ℤ), (67497669 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 2, 11, 2, -9, -3, 1], [0, 1], [-2, 2, 11, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, -1, 3, 11, 2, -9, -3, 1], [0, 1], [-1, 3, 11, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001,
    degreeSevenStageSevenScaledPrefix100Chunk009Part001,
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
