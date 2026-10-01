import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk008Part005

/-! Candidate reduction for Stage Five rows 280 through 289. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part005)))))

theorem degreeSevenStageSevenScaledRows200To299Chunk008_parts :
    degreeSevenStageSevenScaledRows200To299Chunk008 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part004_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008Part005_valid⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008.length =
      147 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008).length =
      80 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk008).length =
      0 := by
  rfl

end

end TraceEuclidean
