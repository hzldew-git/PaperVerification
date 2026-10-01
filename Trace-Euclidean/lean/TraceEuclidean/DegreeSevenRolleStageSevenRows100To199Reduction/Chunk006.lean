import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part009
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part010
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part011
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part012
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part013
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk006Part014

/-! Candidate reduction for Stage Five rows 160 through 169. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part008 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part009 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part010 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part011 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part012 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part013 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014))))))))))))))

theorem degreeSevenStageSevenScaledRows100To199Chunk006_parts :
    degreeSevenStageSevenScaledRows100To199Chunk006 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part007_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part008_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part009_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part010_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part011_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part012_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part013_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006.length =
      352 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006).length =
      144 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006).length =
      2 := by
  rfl

end

end TraceEuclidean
