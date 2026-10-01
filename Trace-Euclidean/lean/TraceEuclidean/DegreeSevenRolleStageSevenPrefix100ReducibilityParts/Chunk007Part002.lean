import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 2 for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk007Part002 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22186296 : ℤ), (-22186293 : ℤ), (-9829438 : ℤ), (-9829435 : ℤ), (-7181569 : ℤ), (-7181566 : ℤ), (-2 : ℤ), (2 : ℤ), (14244556 : ℤ), (14244559 : ℤ), (68094151 : ℤ), (68094154 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (9 : ℤ), (5 : ℤ), (1 : ℤ), (16777216 : ℤ), (-22551973 : ℤ), (-22551970 : ℤ), (-9148619 : ℤ), (-9148616 : ℤ), (-4932861 : ℤ), (-4932858 : ℤ), (-3106331 : ℤ), (-3106328 : ℤ), (14802008 : ℤ), (14802011 : ℤ), (68079180 : ℤ), (68079183 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (1 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-17612870 : ℤ), (-17612867 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-8644782 : ℤ), (-8644779 : ℤ), (6099222 : ℤ), (6099225 : ℤ), (12017485 : ℤ), (12017488 : ℤ), (68059565 : ℤ), (68059568 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (2 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-19570874 : ℤ), (-19570871 : ℤ), (-14144831 : ℤ), (-14144828 : ℤ), (-8718988 : ℤ), (-8718985 : ℤ), (4447767 : ℤ), (4447770 : ℤ), (13083776 : ℤ), (13083779 : ℤ), (68044555 : ℤ), (68044558 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (10 : ℤ), (2 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-18236102 : ℤ), (-18236099 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6701879 : ℤ), (-6701876 : ℤ), (3406222 : ℤ), (3406225 : ℤ), (13407474 : ℤ), (13407477 : ℤ), (68042906 : ℤ), (68042909 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -2, 2, 10, 1, -9, -3, 1], [-1, 1], [0, 2, 0, -10, -11, -2, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007Part002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002,
    degreeSevenStageSevenScaledPrefix100Chunk007Part002,
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
