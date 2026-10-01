import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk004Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk004Part001

/-! Reducibility closure for Stage Five rows 40 through 49. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk004 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001)

theorem degreeSevenStageSevenScaledPrefix100Chunk004_parts :
    degreeSevenStageSevenScaledPrefix100Chunk004 =
      degreeSevenStageSevenScaledPrefix100Chunk004Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk004Part001) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001_valid⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004.length =
      5 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk004_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk004 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk004.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk004_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk004Part001_complete coefficients]

end

end TraceEuclidean
