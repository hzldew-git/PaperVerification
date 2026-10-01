import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 3 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part003 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (3 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20415999 : ℤ), (-20415996 : ℤ), (-12472902 : ℤ), (-12472899 : ℤ), (-8859729 : ℤ), (-8859726 : ℤ), (2993789 : ℤ), (2993792 : ℤ), (13866727 : ℤ), (13866730 : ℤ), (68029518 : ℤ), (68029521 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (3 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19832247 : ℤ), (-19832244 : ℤ), (-14745015 : ℤ), (-14745012 : ℤ), (-6244229 : ℤ), (-6244226 : ℤ), (1816565 : ℤ), (1816568 : ℤ), (14118464 : ℤ), (14118467 : ℤ), (68027866 : ℤ), (68027869 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18746177 : ℤ), (-18746174 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-3711092 : ℤ), (-3711089 : ℤ), (-2 : ℤ), (2 : ℤ), (14349679 : ℤ), (14349682 : ℤ), (68026213 : ℤ), (68026216 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (4 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21033057 : ℤ), (-21033054 : ℤ), (-10590239 : ℤ), (-10590236 : ℤ), (-9313657 : ℤ), (-9313654 : ℤ), (1556310 : ℤ), (1556313 : ℤ), (14507592 : ℤ), (14507595 : ℤ), (68014455 : ℤ), (68014458 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20626945 : ℤ), (-20626942 : ℤ), (-13517723 : ℤ), (-13517720 : ℤ), (-5443240 : ℤ), (-5443237 : ℤ), (-2 : ℤ), (2 : ℤ), (14716514 : ℤ), (14716517 : ℤ), (68012800 : ℤ), (68012803 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 3, 10, 1, -9, -3, 1], [0, 1], [-1, 3, 10, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 4, 10, 1, -9, -3, 1], [1, 1], [0, 0, 4, 6, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003,
    degreeSevenStageSevenScaledPrefix100Chunk007Part003,
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
