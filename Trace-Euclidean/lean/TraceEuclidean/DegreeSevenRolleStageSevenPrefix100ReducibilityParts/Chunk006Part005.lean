import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 5 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part005 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21399866 : ℤ), (-21399863 : ℤ), (-14615993 : ℤ), (-14615990 : ℤ), (-1437733 : ℤ), (-1437730 : ℤ), (-2 : ℤ), (2 : ℤ), (12380480 : ℤ), (12380483 : ℤ), (68214518 : ℤ), (68214521 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22412137 : ℤ), (-22412134 : ℤ), (-10970378 : ℤ), (-10970375 : ℤ), (-6546307 : ℤ), (-6546304 : ℤ), (2311369 : ℤ), (2311372 : ℤ), (12555884 : ℤ), (12555887 : ℤ), (68202972 : ℤ), (68202975 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22175463 : ℤ), (-22175460 : ℤ), (-12706319 : ℤ), (-12706316 : ℤ), (-3066708 : ℤ), (-3066705 : ℤ), (-2 : ℤ), (2 : ℤ), (12888543 : ℤ), (12888546 : ℤ), (68201352 : ℤ), (68201355 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (8 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22766305 : ℤ), (-22766302 : ℤ), (-10269249 : ℤ), (-10269246 : ℤ), (-5355650 : ℤ), (-5355647 : ℤ), (-2 : ℤ), (2 : ℤ), (13344442 : ℤ), (13344445 : ℤ), (68188167 : ℤ), (68188170 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 2, 8, 1, -9, -3, 1], [-1, 1], [0, 0, -2, -10, -11, -2, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005,
    degreeSevenStageSevenScaledPrefix100Chunk006Part005,
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
