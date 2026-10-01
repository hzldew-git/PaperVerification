import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part008
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part009
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part010
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk008Part011

/-! Reducibility closure for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk008 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011)))))))))))

theorem degreeSevenStageSevenScaledPrefix100Chunk008_parts :
    degreeSevenStageSevenScaledPrefix100Chunk008 =
      degreeSevenStageSevenScaledPrefix100Chunk008Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part005 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part006 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part007 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part008 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part009 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part010 ++
    (degreeSevenStageSevenScaledPrefix100Chunk008Part011))))))))))) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008.length =
      25 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk008_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk008 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk008.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk008_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part005_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part006_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part007_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part008_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part009_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part010_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk008Part011_complete coefficients]

end

end TraceEuclidean
