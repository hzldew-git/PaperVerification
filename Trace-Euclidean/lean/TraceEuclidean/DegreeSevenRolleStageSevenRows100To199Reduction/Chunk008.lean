import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk008Part000

/-! Candidate reduction for Stage Five rows 180 through 189. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008Part000

theorem degreeSevenStageSevenScaledRows100To199Chunk008_parts :
    degreeSevenStageSevenScaledRows100To199Chunk008 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008.length =
      19 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008).length =
      11 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk008).length =
      0 := by
  rfl

end

end TraceEuclidean
