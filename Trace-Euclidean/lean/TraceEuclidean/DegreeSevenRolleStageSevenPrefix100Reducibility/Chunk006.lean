import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk006Part005

/-! Reducibility closure for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk006 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005)))))

theorem degreeSevenStageSevenScaledPrefix100Chunk006_parts :
    degreeSevenStageSevenScaledPrefix100Chunk006 =
      degreeSevenStageSevenScaledPrefix100Chunk006Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006Part001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006Part002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006Part003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006Part004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk006Part005))))) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005_valid⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006.length =
      11 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk006_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk006 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk006.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk006_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk006Part005_complete coefficients]

end

end TraceEuclidean
