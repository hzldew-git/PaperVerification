import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk009
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100ReducibilityParts.Chunk009Part008

/-! Reducibility closure for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

def degreeSevenStageSevenFactorCertificatesPrefix100Chunk009 :
    List PolynomialFactorCertificate :=
  degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007 ++
    (degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008))))))))

theorem degreeSevenStageSevenScaledPrefix100Chunk009_parts :
    degreeSevenStageSevenScaledPrefix100Chunk009 =
      degreeSevenStageSevenScaledPrefix100Chunk009Part000 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part001 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part002 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part003 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part004 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part005 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part006 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part007 ++
    (degreeSevenStageSevenScaledPrefix100Chunk009Part008)))))))) := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009_valid :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007_valid,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008_valid⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009_count :
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009.length =
      19 := by
  rfl

theorem degreeSevenStageSevenFactorCertificatesPrefix100Chunk009_complete :
    ∀ coefficients : List ℤ,
      coefficients ∈ degreeSevenStageSevenFinalCoefficients
          degreeSevenStageSevenScaledPrefix100Chunk009 ↔
        coefficients ∈
          degreeSevenStageSevenFactorCertificatesPrefix100Chunk009.map
            PolynomialFactorCertificate.coefficients := by
  intro coefficients
  rw [degreeSevenStageSevenScaledPrefix100Chunk009_parts]
  simp only [degreeSevenStageSevenFinalCoefficients_append,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009,
    List.map_append, List.mem_append]
  rw [degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part000_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part001_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part002_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part003_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part004_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part005_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part006_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part007_complete coefficients,
    degreeSevenStageSevenFactorCertificatesPrefix100Chunk009Part008_complete coefficients]

end

end TraceEuclidean
