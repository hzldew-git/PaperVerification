import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 40 through 49. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk004Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15966420 : ℤ), (-15966417 : ℤ), (-6494528 : ℤ), (-6494525 : ℤ), (2453784 : ℤ), (2453787 : ℤ), (10795459 : ℤ), (10795462 : ℤ), (69130325 : ℤ), (69130328 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (7 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-18814627 : ℤ), (-18814624 : ℤ), (-13392871 : ℤ), (-13392868 : ℤ), (-5551552 : ℤ), (-5551549 : ℤ), (-2 : ℤ), (2 : ℤ), (11783832 : ℤ), (11783835 : ℤ), (69116624 : ℤ), (69116627 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14971535 : ℤ), (-14971532 : ℤ), (-6877560 : ℤ), (-6877557 : ℤ), (-2 : ℤ), (2 : ℤ), (12739207 : ℤ), (12739210 : ℤ), (69028510 : ℤ), (69028513 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (8 : ℤ), (5 : ℤ), (1 : ℤ), (16777216 : ℤ), (-18577036 : ℤ), (-18577033 : ℤ), (-12462833 : ℤ), (-12462830 : ℤ), (-5508503 : ℤ), (-5508500 : ℤ), (-2705138 : ℤ), (-2705135 : ℤ), (13380245 : ℤ), (13380248 : ℤ), (69014669 : ℤ), (69014672 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (-1 : ℤ), (9 : ℤ), (6 : ℤ), (1 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13606318 : ℤ), (-13606315 : ℤ), (-7688668 : ℤ), (-7688665 : ℤ), (-1861233 : ℤ), (-1861230 : ℤ), (14149064 : ℤ), (14149067 : ℤ), (68925776 : ℤ), (68925779 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -1, 2, 7, -1, -9, -3, 1], [0, 1], [-1, 2, 7, -1, -9, -3, 1], 1, 6⟩,
    ⟨[0, 0, 3, 7, -1, -9, -3, 1], [1, 1], [0, 0, 3, 4, -5, -4, 1], 1, 6⟩,
    ⟨[0, 0, 4, 8, -1, -9, -3, 1], [-1, 1], [0, 0, -4, -12, -11, -2, 1], 1, 6⟩,
    ⟨[0, 1, 6, 9, -1, -9, -3, 1], [0, 1], [1, 6, 9, -1, -9, -3, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk004Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000,
    degreeSevenStageSevenScaledPrefix100Chunk004Part000,
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
