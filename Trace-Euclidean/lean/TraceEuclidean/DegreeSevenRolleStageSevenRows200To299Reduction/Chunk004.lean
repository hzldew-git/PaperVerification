import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk004Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk004Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk004Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk004Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk004Part004

/-! Candidate reduction for Stage Five rows 240 through 249. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part004))))

theorem degreeSevenStageSevenScaledRows200To299Chunk004_parts :
    degreeSevenStageSevenScaledRows200To299Chunk004 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part003_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004Part004_valid⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004.length =
      112 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004).length =
      61 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk004).length =
      0 := by
  rfl

end

end TraceEuclidean
