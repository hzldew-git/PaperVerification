import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk001Part000

/-! Reducibility closure for Stage Five rows 10 through 19. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk001 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000

theorem degreeSevenStageSevenScaledPrefix100Chunk001_parts :
    degreeSevenStageSevenScaledPrefix100Chunk001 =
      degreeSevenStageSevenScaledPrefix100Chunk001Part000 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk001_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk001.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000_valid

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk001_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk001.length =
      3 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk001_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk001 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk001.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk001_parts]
  simpa only [degreeSevenStageSevenFactorCertificatesPrefix100Chunk001] using
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk001Part000_complete coefficients

end

end TraceEuclidean
