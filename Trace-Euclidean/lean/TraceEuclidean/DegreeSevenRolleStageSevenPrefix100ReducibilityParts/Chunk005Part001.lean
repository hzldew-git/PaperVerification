import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk005Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (6 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-22083410 : ℤ), (-22083407 : ℤ), (-10623309 : ℤ), (-10623306 : ℤ), (-6113795 : ℤ), (-6113792 : ℤ), (3261142 : ℤ), (3261145 : ℤ), (9899632 : ℤ), (9899635 : ℤ), (68801144 : ℤ), (68801147 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (6 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-21832893 : ℤ), (-21832890 : ℤ), (-12452040 : ℤ), (-12452037 : ℤ), (-1924400 : ℤ), (-1924397 : ℤ), (-2 : ℤ), (2 : ℤ), (10551120 : ℤ), (10551123 : ℤ), (68799618 : ℤ), (68799621 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (6 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-22447720 : ℤ), (-22447717 : ℤ), (-9997159 : ℤ), (-9997156 : ℤ), (-4395393 : ℤ), (-4395390 : ℤ), (-2 : ℤ), (2 : ℤ), (11194587 : ℤ), (11194590 : ℤ), (68787090 : ℤ), (68787093 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19746755 : ℤ), (-19746752 : ℤ), (-14809711 : ℤ), (-14809708 : ℤ), (-5862955 : ℤ), (-5862952 : ℤ), (6480645 : ℤ), (6480648 : ℤ), (8342131 : ℤ), (8342134 : ℤ), (68738049 : ℤ), (68738052 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (0 : ℤ), (7 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-18654329 : ℤ), (-18654326 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-3863970 : ℤ), (-3863967 : ℤ), (3917854 : ℤ), (3917857 : ℤ), (9782555 : ℤ), (9782558 : ℤ), (68736512 : ℤ), (68736515 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, 1, 6, 0, -9, -3, 1], [1, 1], [0, 0, 1, 5, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 2, 6, 0, -9, -3, 1], [0, 1], [0, 2, 6, 0, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001,
    degreeSevenStageSevenScaledPrefix100Chunk005Part001,
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
