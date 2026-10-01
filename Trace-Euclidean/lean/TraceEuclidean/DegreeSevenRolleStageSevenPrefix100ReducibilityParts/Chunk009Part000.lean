import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Reducibility subchunk 0 for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenScaledPrefix100Chunk009Part000 :
    List DegreeSevenStageSevenScaledEntry :=
  [
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (0 : ℤ), (-6 : ℤ), (16777216 : ℤ), (-20080404 : ℤ), (-20080401 : ℤ), (-14435228 : ℤ), (-14435225 : ℤ), (-9958170 : ℤ), (-9958167 : ℤ), (8410204 : ℤ), (8410207 : ℤ), (11656713 : ℤ), (11656716 : ℤ), (67548288 : ℤ), (67548291 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (0 : ℤ), (-5 : ℤ), (16777216 : ℤ), (-19033550 : ℤ), (-19033547 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-8230402 : ℤ), (-8230399 : ℤ), (7236262 : ℤ), (7236265 : ℤ), (12399754 : ℤ), (12399757 : ℤ), (67546557 : ℤ), (67546560 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (1 : ℤ), (-5 : ℤ), (16777216 : ℤ), (-20880125 : ℤ), (-20880122 : ℤ), (-12407714 : ℤ), (-12407711 : ℤ), (-10715944 : ℤ), (-10715941 : ℤ), (6459386 : ℤ), (6459389 : ℤ), (13153195 : ℤ), (13153198 : ℤ), (67532605 : ℤ), (67532608 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (1 : ℤ), (-4 : ℤ), (16777216 : ℤ), (-20353181 : ℤ), (-20353178 : ℤ), (-14960198 : ℤ), (-14960195 : ℤ), (-8198076 : ℤ), (-8198073 : ℤ), (5583951 : ℤ), (5583954 : ℤ), (13538038 : ℤ), (13538041 : ℤ), (67530870 : ℤ), (67530873 : ℤ)⟩,
    ⟨(-3 : ℤ), (-9 : ℤ), (2 : ℤ), (11 : ℤ), (1 : ℤ), (-3 : ℤ), (16777216 : ℤ), (-19488367 : ℤ), (-19488364 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-6669624 : ℤ), (-6669621 : ℤ), (4680184 : ℤ), (4680187 : ℤ), (13867293 : ℤ), (13867296 : ℤ), (67529135 : ℤ), (67529138 : ℤ)⟩
  ]

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000 :
    List PolynomialFactorCertificate :=
  [
    ⟨[0, -3, 1, 11, 2, -9, -3, 1], [-1, 1], [0, 3, 2, -9, -11, -2, 1], 1, 6⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every displayed nontrivial factorization.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

set_option maxHeartbeats 0 in
-- Exact interval evaluation identifies all final coefficients in this part.
theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009Part000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  norm_num (config := { maxSteps := 300000 })
    [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000,
    degreeSevenStageSevenScaledPrefix100Chunk009Part000,
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
