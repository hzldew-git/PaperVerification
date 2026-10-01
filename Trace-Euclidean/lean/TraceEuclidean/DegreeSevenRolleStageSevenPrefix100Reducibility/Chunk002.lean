import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk002Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk002Part001

/-! Reducibility closure for Stage Five rows 20 through 29. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk002 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001)

theorem degreeSevenStageSevenScaledPrefix100Chunk002_parts :
    degreeSevenStageSevenScaledPrefix100Chunk002 =
      degreeSevenStageSevenScaledPrefix100Chunk002Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk002Part001) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001_valid⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002.length =
      4 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk002_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk002 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk002.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk002_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk002Part001_complete coefficients]

end

end TraceEuclidean
