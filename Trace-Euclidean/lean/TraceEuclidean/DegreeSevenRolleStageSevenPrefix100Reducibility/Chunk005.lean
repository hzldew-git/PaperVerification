import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk005Part006

/-! Reducibility closure for Stage Five rows 50 through 59. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk005 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006))))))

theorem degreeSevenStageSevenScaledPrefix100Chunk005_parts :
    degreeSevenStageSevenScaledPrefix100Chunk005 =
      degreeSevenStageSevenScaledPrefix100Chunk005Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part005 ++
    (degreeSevenStageSevenScaledPrefix100Chunk005Part006)))))) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006_valid⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005.length =
      12 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk005_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk005 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk005.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk005_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part005_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk005Part006_complete coefficients]

end

end TraceEuclidean
