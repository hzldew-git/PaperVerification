import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk008Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (6 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24220895 : ℤ), (-24220892 : ℤ), (-13369458 : ℤ), (-13369455 : ℤ), (-2 : ℤ), (2 : ℤ), (3895722 : ℤ), (3895725 : ℤ), (8857180 : ℤ), (8857183 : ℤ), (67978856 : ℤ), (67978859 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (6 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24723706 : ℤ), (-24723703 : ℤ), (-11251381 : ℤ), (-11251378 : ℤ), (-3379038 : ℤ), (-3379035 : ℤ), (5560687 : ℤ), (5560690 : ℤ), (8967709 : ℤ), (8967712 : ℤ), (67967133 : ℤ), (67967136 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (6 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24603789 : ℤ), (-24603786 : ℤ), (-12207200 : ℤ), (-12207197 : ℤ), (-2 : ℤ), (2 : ℤ), (1832118 : ℤ), (1832121 : ℤ), (10154794 : ℤ), (10154797 : ℤ), (67965481 : ℤ), (67965484 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (6 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-25052064 : ℤ), (-25052061 : ℤ), (-9440914 : ℤ), (-9440911 : ℤ), (-4720586 : ℤ), (-4720583 : ℤ), (4060868 : ℤ), (4060871 : ℤ), (10340359 : ℤ), (10340362 : ℤ), (67953741 : ℤ), (67953744 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (6 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25254870 : ℤ), (-25254867 : ℤ), (-9219853 : ℤ), (-9219850 : ℤ), (-2047542 : ℤ), (-2047539 : ℤ), (-2 : ℤ), (2 : ℤ), (11724999 : ℤ), (11725002 : ℤ), (67938672 : ℤ), (67938675 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, -2, 6, 2, -9, -3, 1], [0, 1], [0, -2, 6, 2, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, -1, 6, 2, -9, -3, 1], [1, 1], [0, 0, -1, 7, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 1, 6, 2, -9, -3, 1], [0, 1], [0, 1, 6, 2, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001,
    degreeSevenStageSevenScaledPrefix100Chunk008Part001,
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
