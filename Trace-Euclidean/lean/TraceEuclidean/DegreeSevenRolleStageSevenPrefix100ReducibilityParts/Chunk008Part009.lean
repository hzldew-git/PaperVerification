import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 9 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part009 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (-1 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-19990402 : ℤ), (-19990399 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6525232 : ℤ), (-6525229 : ℤ), (7913408 : ℤ), (7913411 : ℤ), (10878282 : ℤ), (10878285 : ℤ), (67642564 : ℤ), (67642567 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (0 : ℤ), (-5 : ℤ), (16777216 : ℤ), (-21742073 : ℤ), (-21742070 : ℤ), (-11745846 : ℤ), (-11745843 : ℤ), (-10249476 : ℤ), (-10249473 : ℤ), (7998960 : ℤ), (7998963 : ℤ), (11249379 : ℤ), (11249382 : ℤ), (67630459 : ℤ), (67630462 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (0 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-21395326 : ℤ), (-21395323 : ℤ), (-14106849 : ℤ), (-14106846 : ℤ), (-7731934 : ℤ), (-7731931 : ℤ), (6705832 : ℤ), (6705835 : ℤ), (12040937 : ℤ), (12040940 : ℤ), (67628744 : ℤ), (67628747 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (0 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-20960954 : ℤ), (-20960951 : ℤ), (-15476897 : ℤ), (-15476894 : ℤ), (-6205886 : ℤ), (-6205883 : ℤ), (5581707 : ℤ), (5581710 : ℤ), (12576405 : ℤ), (12576408 : ℤ), (67627028 : ℤ), (67627031 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20344416 : ℤ), (-20344413 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-4792636 : ℤ), (-4792633 : ℤ), (4430670 : ℤ), (4430673 : ℤ), (12999692 : ℤ), (12999695 : ℤ), (67625312 : ℤ), (67625315 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -3, 0, 10, 2, -9, -3, 1], [0, 1], [-3, 0, 10, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part009 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009,
    degreeSevenStageSevenScaledPrefix100Chunk008Part009,
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
