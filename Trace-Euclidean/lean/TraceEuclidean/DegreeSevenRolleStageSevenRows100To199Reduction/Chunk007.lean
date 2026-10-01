import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk007Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk007Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk007Part002

/-! Candidate reduction for Stage Five rows 170 through 179. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part002))

theorem degreeSevenStageSevenScaledRows100To199Chunk007_parts :
    degreeSevenStageSevenScaledRows100To199Chunk007 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part001_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007Part002_valid⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007.length =
      61 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007).length =
      36 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk007).length =
      0 := by
  rfl

end

end TraceEuclidean
