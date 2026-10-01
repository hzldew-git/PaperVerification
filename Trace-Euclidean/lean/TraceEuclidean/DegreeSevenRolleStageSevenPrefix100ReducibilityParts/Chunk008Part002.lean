import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 2 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part002 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22565690 : ℤ), (-22565687 : ℤ), (-16086246 : ℤ), (-16086243 : ℤ), (-2 : ℤ), (2 : ℤ), (5540115 : ℤ), (5540118 : ℤ), (8342409 : ℤ), (8342412 : ℤ), (67910817 : ℤ), (67910820 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23405607 : ℤ), (-23405604 : ℤ), (-14107096 : ℤ), (-14107093 : ℤ), (-2472369 : ℤ), (-2472366 : ℤ), (6911760 : ℤ), (6911763 : ℤ), (8315695 : ℤ), (8315698 : ℤ), (67899020 : ℤ), (67899023 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23210570 : ℤ), (-23210567 : ℤ), (-14829234 : ℤ), (-14829231 : ℤ), (-2 : ℤ), (2 : ℤ), (3234046 : ℤ), (3234049 : ℤ), (10049807 : ℤ), (10049810 : ℤ), (67897356 : ℤ), (67897359 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-24031046 : ℤ), (-24031043 : ℤ), (-11731914 : ℤ), (-11731911 : ℤ), (-5116504 : ℤ), (-5116501 : ℤ), (7974256 : ℤ), (7974259 : ℤ), (8159403 : ℤ), (8159406 : ℤ), (67887209 : ℤ), (67887212 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (7 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23881873 : ℤ), (-23881870 : ℤ), (-12785091 : ℤ), (-12785088 : ℤ), (-3125898 : ℤ), (-3125895 : ℤ), (4795557 : ℤ), (4795560 : ℤ), (10253168 : ℤ), (10253171 : ℤ), (67885542 : ℤ), (67885545 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, -1, 7, 2, -9, -3, 1], [0, 1], [-1, -1, 7, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002,
    degreeSevenStageSevenScaledPrefix100Chunk008Part002,
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
