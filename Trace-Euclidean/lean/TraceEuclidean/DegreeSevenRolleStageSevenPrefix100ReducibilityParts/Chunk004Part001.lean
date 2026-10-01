import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 40 through 49. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk004Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23004265 : ℤ), (-23004262 : ℤ), (-12107066 : ℤ), (-12107063 : ℤ), (-2 : ℤ), (2 : ℤ), (3318759 : ℤ), (3318762 : ℤ), (5956646 : ℤ), (5956649 : ℤ), (68977332 : ℤ), (68977335 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23862876 : ℤ), (-23862873 : ℤ), (-7898556 : ℤ), (-7898553 : ℤ), (-3195263 : ℤ), (-3195260 : ℤ), (-2 : ℤ), (2 : ℤ), (9145414 : ℤ), (9145417 : ℤ), (68952686 : ℤ), (68952689 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 4, 0, -9, -3, 1], [0, 1], [0, 1, 4, 0, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk004Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001,
    degreeSevenStageSevenScaledPrefix100Chunk004Part001,
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
