import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk004Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk004Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk004Part002

/-! Candidate reduction for Stage Five rows 140 through 149. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002))

theorem degreeSevenStageSevenScaledRows100To199Chunk004_parts :
    degreeSevenStageSevenScaledRows100To199Chunk004 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part001_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002_valid⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004.length =
      51 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004).length =
      26 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004).length =
      0 := by
  rfl

end

end TraceEuclidean
