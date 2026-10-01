import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk000Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk000Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk000Part002

/-! Candidate reduction for Stage Five rows 100 through 109. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002))

theorem degreeSevenStageSevenScaledRows100To199Chunk000_parts :
    degreeSevenStageSevenScaledRows100To199Chunk000 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part001_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002_valid⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000.length =
      57 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000).length =
      26 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000).length =
      0 := by
  rfl

end

end TraceEuclidean
