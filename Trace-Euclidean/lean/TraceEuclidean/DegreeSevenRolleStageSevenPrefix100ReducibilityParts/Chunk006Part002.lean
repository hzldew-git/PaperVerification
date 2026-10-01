import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 2 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part002 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (6 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24160071 : ℤ), (-24160068 : ℤ), (-7728117 : ℤ), (-7728114 : ℤ), (-5069648 : ℤ), (-5069645 : ℤ), (-2 : ℤ), (2 : ℤ), (11738255 : ℤ), (11738258 : ℤ), (68360987 : ℤ), (68360990 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19362298 : ℤ), (-19362295 : ℤ), (-18424487 : ℤ), (-18424484 : ℤ), (-2 : ℤ), (2 : ℤ), (3382225 : ℤ), (3382228 : ℤ), (9212389 : ℤ), (9212392 : ℤ), (68333575 : ℤ), (68333578 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-21682012 : ℤ), (-21682009 : ℤ), (-14823717 : ℤ), (-14823714 : ℤ), (-3073784 : ℤ), (-3073781 : ℤ), (5047087 : ℤ), (5047090 : ℤ), (9351665 : ℤ), (9351668 : ℤ), (68322165 : ℤ), (68322168 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21310214 : ℤ), (-21310211 : ℤ), (-15788690 : ℤ), (-15788687 : ℤ), (-2 : ℤ), (2 : ℤ), (1601120 : ℤ), (1601123 : ℤ), (10318622 : ℤ), (10318625 : ℤ), (68320567 : ℤ), (68320570 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (7 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-22638643 : ℤ), (-22638640 : ℤ), (-11676920 : ℤ), (-11676917 : ℤ), (-6278263 : ℤ), (-6278260 : ℤ), (5901803 : ℤ), (5901806 : ℤ), (9522685 : ℤ), (9522688 : ℤ), (68310741 : ℤ), (68310744 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002 :
    List PolynomialFactorCertificate :=
  [

  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002,
    degreeSevenStageSevenScaledPrefix100Chunk006Part002,
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
