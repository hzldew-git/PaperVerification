import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 11 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part011 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22107704 : ℤ), (-22107701 : ℤ), (-13680705 : ℤ), (-13680702 : ℤ), (-5101020 : ℤ), (-5101017 : ℤ), (2136498 : ℤ), (2136501 : ℤ), (14298461 : ℤ), (14298464 : ℤ), (67595873 : ℤ), (67595876 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21803819 : ℤ), (-21803816 : ℤ), (-14788536 : ℤ), (-14788533 : ℤ), (-2397302 : ℤ), (-2397299 : ℤ), (-2 : ℤ), (2 : ℤ), (14536912 : ℤ), (14536915 : ℤ), (67594150 : ℤ), (67594153 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (3 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22755050 : ℤ), (-22755047 : ℤ), (-11326950 : ℤ), (-11326947 : ℤ), (-6872743 : ℤ), (-6872740 : ℤ), (1809764 : ℤ), (1809767 : ℤ), (14704404 : ℤ), (14704407 : ℤ), (67581979 : ℤ), (67581982 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22532799 : ℤ), (-22532796 : ℤ), (-12952667 : ℤ), (-12952664 : ℤ), (-3871963 : ℤ), (-3871960 : ℤ), (-2 : ℤ), (2 : ℤ), (14918581 : ℤ), (14918584 : ℤ), (67580253 : ℤ), (67580256 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (10 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23097642 : ℤ), (-23097639 : ℤ), (-10574478 : ℤ), (-10574475 : ℤ), (-6026753 : ℤ), (-6026750 : ℤ), (-2 : ℤ), (2 : ℤ), (15273944 : ℤ), (15273947 : ℤ), (67566334 : ℤ), (67566337 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 2, 10, 2, -9, -3, 1], [0, 1], [-1, 2, 10, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 3, 10, 2, -9, -3, 1], [1, 1], [0, 0, 3, 7, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part011 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011,
    degreeSevenStageSevenScaledPrefix100Chunk008Part011,
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
