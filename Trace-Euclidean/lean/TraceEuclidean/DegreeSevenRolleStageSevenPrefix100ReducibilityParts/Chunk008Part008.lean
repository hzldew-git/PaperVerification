import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 8 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part008 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22775769 : ℤ), (-22775766 : ℤ), (-13297328 : ℤ), (-13297325 : ℤ), (-4400062 : ℤ), (-4400059 : ℤ), (2663922 : ℤ), (2663925 : ℤ), (13257398 : ℤ), (13257401 : ℤ), (67693243 : ℤ), (67693246 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22542510 : ℤ), (-22542507 : ℤ), (-14288858 : ℤ), (-14288855 : ℤ), (-1284015 : ℤ), (-1284012 : ℤ), (-2 : ℤ), (2 : ℤ), (13565249 : ℤ), (13565252 : ℤ), (67691539 : ℤ), (67691542 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-23316089 : ℤ), (-23316086 : ℤ), (-11295723 : ℤ), (-11295720 : ℤ), (-5881769 : ℤ), (-5881766 : ℤ), (2210810 : ℤ), (2210813 : ℤ), (13744691 : ℤ), (13744694 : ℤ), (67679484 : ℤ), (67679487 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23132249 : ℤ), (-23132246 : ℤ), (-12687379 : ℤ), (-12687376 : ℤ), (-2729075 : ℤ), (-2729072 : ℤ), (-2 : ℤ), (2 : ℤ), (14012331 : ℤ), (14012334 : ℤ), (67677777 : ℤ), (67677780 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (9 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23616528 : ℤ), (-23616525 : ℤ), (-10710846 : ℤ), (-10710843 : ℤ), (-4616006 : ℤ), (-4616003 : ℤ), (-2 : ℤ), (2 : ℤ), (14420791 : ℤ), (14420794 : ℤ), (67663994 : ℤ), (67663997 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 1, 9, 2, -9, -3, 1], [-1, 1], [0, 1, 0, -9, -11, -2, 1], 1, 6⟩,
    ⟨[0, 0, 1, 9, 2, -9, -3, 1], [0, 1], [0, 1, 9, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 2, 9, 2, -9, -3, 1], [1, 1], [0, 0, 2, 7, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 3, 9, 2, -9, -3, 1], [0, 1], [0, 3, 9, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part008 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008,
    degreeSevenStageSevenScaledPrefix100Chunk008Part008,
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
