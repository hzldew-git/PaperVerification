import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 4 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part004 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (4 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-20800696 : ℤ), (-20800693 : ℤ), (-13040109 : ℤ), (-13040106 : ℤ), (-8776318 : ℤ), (-8776315 : ℤ), (2504959 : ℤ), (2504962 : ℤ), (15853200 : ℤ), (15853203 : ℤ), (67400367 : ℤ), (67400370 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (4 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-20268993 : ℤ), (-20268990 : ℤ), (-15019558 : ℤ), (-15019555 : ℤ), (-6487919 : ℤ), (-6487916 : ℤ), (1493315 : ℤ), (1493318 : ℤ), (16025954 : ℤ), (16025957 : ℤ), (67398604 : ℤ), (67398607 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19388172 : ℤ), (-19388169 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-4280046 : ℤ), (-4280043 : ℤ), (-2 : ℤ), (2 : ℤ), (16189999 : ℤ), (16190002 : ℤ), (67396842 : ℤ), (67396845 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (5 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21393574 : ℤ), (-21393571 : ℤ), (-11496510 : ℤ), (-11496507 : ℤ), (-8998746 : ℤ), (-8998743 : ℤ), (1307439 : ℤ), (1307442 : ℤ), (16338363 : ℤ), (16338366 : ℤ), (67384432 : ℤ), (67384435 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (12 : ℤ), (5 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21015764 : ℤ), (-21015761 : ℤ), (-13841980 : ℤ), (-13841977 : ℤ), (-5874425 : ℤ), (-5874422 : ℤ), (-2 : ℤ), (2 : ℤ), (16490909 : ℤ), (16490912 : ℤ), (67382666 : ℤ), (67382669 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 4, 12, 2, -9, -3, 1], [0, 1], [-1, 4, 12, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 5, 12, 2, -9, -3, 1], [1, 1], [0, 0, 5, 7, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004,
    degreeSevenStageSevenScaledPrefix100Chunk009Part004,
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
