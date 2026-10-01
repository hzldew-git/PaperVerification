import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk002Part007

/-! Candidate reduction for Stage Five rows 220 through 229. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007)))))))

theorem degreeSevenStageSevenScaledRows200To299Chunk002_parts :
    degreeSevenStageSevenScaledRows200To299Chunk002 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part006_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007_valid⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002.length =
      183 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002).length =
      93 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002).length =
      2 := by
  rfl

end

end TraceEuclidean
