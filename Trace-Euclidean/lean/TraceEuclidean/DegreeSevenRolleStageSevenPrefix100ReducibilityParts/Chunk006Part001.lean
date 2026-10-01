import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22149225 : ℤ), (-22149222 : ℤ), (-15171020 : ℤ), (-15171017 : ℤ), (-2 : ℤ), (2 : ℤ), (4220783 : ℤ), (4220786 : ℤ), (7828128 : ℤ), (7828131 : ℤ), (68412738 : ℤ), (68412741 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23010289 : ℤ), (-23010286 : ℤ), (-12814254 : ℤ), (-12814251 : ℤ), (-3305217 : ℤ), (-3305214 : ℤ), (6385265 : ℤ), (6385268 : ℤ), (7484486 : ℤ), (7484489 : ℤ), (68401412 : ℤ), (68401415 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22807625 : ℤ), (-22807622 : ℤ), (-13751830 : ℤ), (-13751827 : ℤ), (-2 : ℤ), (2 : ℤ), (1878806 : ℤ), (1878809 : ℤ), (9422226 : ℤ), (9422229 : ℤ), (68399828 : ℤ), (68399831 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23496579 : ℤ), (-23496576 : ℤ), (-11049666 : ℤ), (-11049663 : ℤ), (-4464218 : ℤ), (-4464215 : ℤ), (4204808 : ℤ), (4204811 : ℤ), (9558572 : ℤ), (9558575 : ℤ), (68388486 : ℤ), (68388489 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23773285 : ℤ), (-23773282 : ℤ), (-10599498 : ℤ), (-10599495 : ℤ), (-1981887 : ℤ), (-1981884 : ℤ), (-2 : ℤ), (2 : ℤ), (11122123 : ℤ), (11122126 : ℤ), (68373952 : ℤ), (68373955 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, -1, 6, 1, -9, -3, 1], [0, 1], [0, -1, 6, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, -1, 0, 6, 1, -9, -3, 1], [0, 1], [-1, 0, 6, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 6, 1, -9, -3, 1], [0, 1], [0, 1, 6, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001,
    degreeSevenStageSevenScaledPrefix100Chunk006Part001,
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
