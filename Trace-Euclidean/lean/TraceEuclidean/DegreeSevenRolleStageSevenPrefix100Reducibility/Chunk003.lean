import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk003Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk003Part001

/-! Reducibility closure for Stage Five rows 30 through 39. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk003 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001)

theorem degreeSevenStageSevenScaledPrefix100Chunk003_parts :
    degreeSevenStageSevenScaledPrefix100Chunk003 =
      degreeSevenStageSevenScaledPrefix100Chunk003Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk003Part001) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001_valid⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003.length =
      4 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk003_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk003 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk003.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk003_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk003Part001_complete coefficients]

end

end TraceEuclidean
