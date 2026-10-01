import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-21290061 : ℤ), (-21290058 : ℤ), (-12048631 : ℤ), (-12048628 : ℤ), (-8007658 : ℤ), (-8007655 : ℤ), (3554830 : ℤ), (3554833 : ℤ), (12808906 : ℤ), (12808909 : ℤ), (68124017 : ℤ), (68124020 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-20910753 : ℤ), (-20910750 : ℤ), (-13948842 : ℤ), (-13948839 : ℤ), (-5484867 : ℤ), (-5484864 : ℤ), (2224890 : ℤ), (2224893 : ℤ), (13138594 : ℤ), (13138597 : ℤ), (68122382 : ℤ), (68122385 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-20421007 : ℤ), (-20421004 : ℤ), (-15338806 : ℤ), (-15338803 : ℤ), (-2650390 : ℤ), (-2650387 : ℤ), (-2 : ℤ), (2 : ℤ), (13430861 : ℤ), (13430864 : ℤ), (68120747 : ℤ), (68120750 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (3 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21772383 : ℤ), (-21772380 : ℤ), (-10877381 : ℤ), (-10877378 : ℤ), (-7782103 : ℤ), (-7782100 : ℤ), (1866480 : ℤ), (1866483 : ℤ), (13597694 : ℤ), (13597697 : ℤ), (68109097 : ℤ), (68109100 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21472867 : ℤ), (-21472864 : ℤ), (-13033474 : ℤ), (-13033471 : ℤ), (-4314331 : ℤ), (-4314328 : ℤ), (-2 : ℤ), (2 : ℤ), (13854617 : ℤ), (13854620 : ℤ), (68107459 : ℤ), (68107462 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 2, 9, 1, -9, -3, 1], [-1, 1], [0, 1, -1, -10, -11, -2, 1], 1, 6⟩,
    ⟨[0, 0, 3, 9, 1, -9, -3, 1], [1, 1], [0, 0, 3, 6, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001,
    degreeSevenStageSevenScaledPrefix100Chunk007Part001,
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
