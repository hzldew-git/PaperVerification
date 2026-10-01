import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk000Part000

/-! Reducibility closure for Stage Five rows 0 through 9. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk000 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk000Part000

theorem degreeSevenStageSevenScaledPrefix100Chunk000_parts :
    degreeSevenStageSevenScaledPrefix100Chunk000 =
      degreeSevenStageSevenScaledPrefix100Chunk000Part000 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk000_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk000.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFactorCertificatesPrefix100Chunk000Part000_valid

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk000_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk000.length =
      0 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk000_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk000 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk000.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk000_parts]
  simpa only [degreeSevenStageSevenFactorCertificatesPrefix100Chunk000] using
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk000Part000_complete coefficients

end

end TraceEuclidean
