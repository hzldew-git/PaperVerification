import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk006Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24636960 : ℤ), (-24636957 : ℤ), (-10749203 : ℤ), (-10749200 : ℤ), (-2 : ℤ), (2 : ℤ), (3001428 : ℤ), (3001431 : ℤ), (6969299 : ℤ), (6969302 : ℤ), (68556841 : ℤ), (68556844 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (4 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25250375 : ℤ), (-25250372 : ℤ), (-6203990 : ℤ), (-6203987 : ℤ), (-3643857 : ℤ), (-3643854 : ℤ), (-2 : ℤ), (2 : ℤ), (9708276 : ℤ), (9708280 : ℤ), (68531351 : ℤ), (68531354 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23826415 : ℤ), (-23826412 : ℤ), (-12162927 : ℤ), (-12162924 : ℤ), (-2 : ℤ), (2 : ℤ), (2288007 : ℤ), (2288010 : ℤ), (8364157 : ℤ), (8364160 : ℤ), (68478583 : ℤ), (68478586 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (5 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24344810 : ℤ), (-24344807 : ℤ), (-8812752 : ℤ), (-8812749 : ℤ), (-5364078 : ℤ), (-5364075 : ℤ), (4837241 : ℤ), (4837244 : ℤ), (8358478 : ℤ), (8358481 : ℤ), (68467325 : ℤ), (68467328 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (1 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24570201 : ℤ), (-24570198 : ℤ), (-8689417 : ℤ), (-8689414 : ℤ), (-2489624 : ℤ), (-2489621 : ℤ), (-2 : ℤ), (2 : ℤ), (10437746 : ℤ), (10437749 : ℤ), (68452902 : ℤ), (68452905 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, 0, -1, 4, 1, -9, -3, 1], [0, 1], [0, -1, 4, 1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, -1, 5, 1, -9, -3, 1], [1, 1], [0, 0, -1, 6, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 1, 5, 1, -9, -3, 1], [0, 1], [0, 1, 5, 1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000,
    degreeSevenStageSevenScaledPrefix100Chunk006Part000,
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
