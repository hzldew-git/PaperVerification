import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 8 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part008 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (15 : ℤ), (11 : ℤ), (3 : ℤ), (16777216 : ℤ), (-20156095 : ℤ), (-20156092 : ℤ), (-11512108 : ℤ), (-11512105 : ℤ), (-7266480 : ℤ), (-7266477 : ℤ), (-4358080 : ℤ), (-4358077 : ℤ), (19404048 : ℤ), (19404051 : ℤ), (67030119 : ℤ), (67030122 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (16 : ℤ), (11 : ℤ), (2 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15699010 : ℤ), (-15699007 : ℤ), (-8934548 : ℤ), (-8934545 : ℤ), (-2056719 : ℤ), (-2056716 : ℤ), (19665451 : ℤ), (19665454 : ℤ), (66943448 : ℤ), (66943451 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (16 : ℤ), (12 : ℤ), (3 : ℤ), (16777216 : ℤ), (-18963575 : ℤ), (-18963572 : ℤ), (-11934137 : ℤ), (-11934134 : ℤ), (-9496168 : ℤ), (-9496165 : ℤ), (-3332272 : ℤ), (-3332269 : ℤ), (19940830 : ℤ), (19940833 : ℤ), (66926726 : ℤ), (66926729 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (17 : ℤ), (13 : ℤ), (3 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13949197 : ℤ), (-13949194 : ℤ), (-10596230 : ℤ), (-10596227 : ℤ), (-2818916 : ℤ), (-2818913 : ℤ), (20460606 : ℤ), (20460609 : ℤ), (66822357 : ℤ), (66822360 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 2, 11, 16, 2, -9, -3, 1], [0, 1], [2, 11, 16, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 3, 13, 17, 2, -9, -3, 1], [0, 1], [3, 13, 17, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part008 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008,
    degreeSevenStageSevenScaledPrefix100Chunk009Part008,
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
