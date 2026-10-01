import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part007
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk000Part008

/-! Candidate reduction for Stage Five rows 200 through 209. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part008))))))))

theorem degreeSevenStageSevenScaledRows200To299Chunk000_parts :
    degreeSevenStageSevenScaledRows200To299Chunk000 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part007_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000Part008_valid⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000.length =
      219 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000).length =
      100 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk000).length =
      1 := by
  rfl

end

end TraceEuclidean
