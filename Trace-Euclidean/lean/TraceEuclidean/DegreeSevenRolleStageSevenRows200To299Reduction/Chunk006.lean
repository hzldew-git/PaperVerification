import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part007
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part008
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part009
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part010
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part011
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part012
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part013
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part014
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk006Part015

/-! Candidate reduction for Stage Five rows 260 through 269. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part008 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part009 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part010 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part011 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part012 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part013 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part014 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015)))))))))))))))

theorem degreeSevenStageSevenScaledRows200To299Chunk006_parts :
    degreeSevenStageSevenScaledRows200To299Chunk006 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part007_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part008_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part009_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part010_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part011_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part012_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part013_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part014_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006.length =
      381 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006).length =
      200 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006).length =
      7 := by
  rfl

end

end TraceEuclidean
