import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 1 for Stage Five rows 30 through 39. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk003Part001 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-19740198 : ℤ), (-19740195 : ℤ), (-10791161 : ℤ), (-10791158 : ℤ), (-9300144 : ℤ), (-9300141 : ℤ), (5967164 : ℤ), (5967167 : ℤ), (7786598 : ℤ), (7786601 : ℤ), (69219144 : ℤ), (69219147 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-19078480 : ℤ), (-19078477 : ℤ), (-14036096 : ℤ), (-14036093 : ℤ), (-5565334 : ℤ), (-5565331 : ℤ), (3330342 : ℤ), (3330345 : ℤ), (9273295 : ℤ), (9273298 : ℤ), (69217677 : ℤ), (69217680 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-17436516 : ℤ), (-17436513 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-1873322 : ℤ), (-1873319 : ℤ), (-2 : ℤ), (2 : ℤ), (10012252 : ℤ), (10012255 : ℤ), (69216210 : ℤ), (69216213 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (6 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-19932832 : ℤ), (-19932829 : ℤ), (-12776811 : ℤ), (-12776808 : ℤ), (-4034623 : ℤ), (-4034620 : ℤ), (-2 : ℤ), (2 : ℤ), (10681578 : ℤ), (10681581 : ℤ), (69204092 : ℤ), (69204095 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 1, 6, -1, -9, -3, 1], [0, 1], [-1, 1, 6, -1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 2, 6, -1, -9, -3, 1], [1, 1], [0, 0, 2, 4, -5, -4, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk003Part001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001,
    degreeSevenStageSevenScaledPrefix100Chunk003Part001,
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
