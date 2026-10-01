import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 4 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part004 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (11 : ℤ), (2 : ℤ), (-5 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15515572 : ℤ), (-15515569 : ℤ), (-11541248 : ℤ), (-11541245 : ℤ), (5993743 : ℤ), (5993746 : ℤ), (13015457 : ℤ), (13015460 : ℤ), (67966241 : ℤ), (67966244 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (11 : ℤ), (4 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19251928 : ℤ), (-19251925 : ℤ), (-13317974 : ℤ), (-13317971 : ℤ), (-9586525 : ℤ), (-9586522 : ℤ), (2581362 : ℤ), (2581365 : ℤ), (14782228 : ℤ), (14782231 : ℤ), (67934240 : ℤ), (67934243 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (11 : ℤ), (4 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-17562952 : ℤ), (-17562949 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6962335 : ℤ), (-6962332 : ℤ), (1525412 : ℤ), (1525415 : ℤ), (14985926 : ℤ), (14985929 : ℤ), (67932570 : ℤ), (67932573 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (11 : ℤ), (5 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19506885 : ℤ), (-19506882 : ℤ), (-14310769 : ℤ), (-14310766 : ℤ), (-6460609 : ℤ), (-6460606 : ℤ), (-2 : ℤ), (2 : ℤ), (15502310 : ℤ), (15502313 : ℤ), (67917358 : ℤ), (67917361 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (11 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-20348196 : ℤ), (-20348193 : ℤ), (-12945035 : ℤ), (-12945032 : ℤ), (-5345821 : ℤ), (-5345818 : ℤ), (-2086976 : ℤ), (-2086973 : ℤ), (15965311 : ℤ), (15965314 : ℤ), (67902120 : ℤ), (67902123 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 4, 11, 1, -9, -3, 1], [0, 1], [-1, 4, 11, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 5, 11, 1, -9, -3, 1], [1, 1], [0, 0, 5, 6, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004,
    degreeSevenStageSevenScaledPrefix100Chunk007Part004,
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
