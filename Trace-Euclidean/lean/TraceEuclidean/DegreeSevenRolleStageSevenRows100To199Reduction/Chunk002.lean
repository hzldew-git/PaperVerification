import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk002Part000

/-! Candidate reduction for Stage Five rows 120 through 129. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000

theorem degreeSevenStageSevenScaledRows100To199Chunk002_parts :
    degreeSevenStageSevenScaledRows100To199Chunk002 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002.length =
      7 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002).length =
      0 := by
  rfl

end

end TraceEuclidean
