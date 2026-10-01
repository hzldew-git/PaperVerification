import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 5 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part005 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22553401 : ℤ), (-22553398 : ℤ), (-15278568 : ℤ), (-15278565 : ℤ), (-2 : ℤ), (2 : ℤ), (1378352 : ℤ), (1378355 : ℤ), (11793304 : ℤ), (11793307 : ℤ), (67801718 : ℤ), (67801721 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-23533748 : ℤ), (-23533745 : ℤ), (-11832542 : ℤ), (-11832539 : ℤ), (-5808925 : ℤ), (-5808922 : ℤ), (5074255 : ℤ), (5074258 : ℤ), (11450885 : ℤ), (11450888 : ℤ), (67791478 : ℤ), (67791481 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23359190 : ℤ), (-23359187 : ℤ), (-13008888 : ℤ), (-13008885 : ℤ), (-3732056 : ℤ), (-3732053 : ℤ), (3453877 : ℤ), (3453880 : ℤ), (11997866 : ℤ), (11997869 : ℤ), (67789794 : ℤ), (67789797 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23824295 : ℤ), (-23824292 : ℤ), (-11275628 : ℤ), (-11275625 : ℤ), (-4956696 : ℤ), (-4956693 : ℤ), (2795943 : ℤ), (2795946 : ℤ), (12625912 : ℤ), (12625915 : ℤ), (67776166 : ℤ), (67776169 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (8 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23667861 : ℤ), (-23667858 : ℤ), (-12487003 : ℤ), (-12487000 : ℤ), (-1460487 : ℤ), (-1460484 : ℤ), (-2 : ℤ), (2 : ℤ), (12982277 : ℤ), (12982280 : ℤ), (67774478 : ℤ), (67774481 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 0, 8, 2, -9, -3, 1], [0, 1], [-1, 0, 8, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, -1, 1, 8, 2, -9, -3, 1], [0, 1], [-1, 1, 8, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 1, 8, 2, -9, -3, 1], [-1, 1], [0, 0, -1, -9, -11, -2, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005,
    degreeSevenStageSevenScaledPrefix100Chunk008Part005,
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
