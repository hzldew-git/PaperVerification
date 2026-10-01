import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk007Part006

/-! Reducibility closure for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk007 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006))))))

theorem degreeSevenStageSevenScaledPrefix100Chunk007_parts :
    degreeSevenStageSevenScaledPrefix100Chunk007 =
      degreeSevenStageSevenScaledPrefix100Chunk007Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part005 ++
    (degreeSevenStageSevenScaledPrefix100Chunk007Part006)))))) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006_valid⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007.length =
      12 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk007_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk007 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk007.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk007_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part005_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk007Part006_complete coefficients]

end

end TraceEuclidean
