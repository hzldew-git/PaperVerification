import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk005Part000

/-! Candidate reduction for Stage Five rows 250 through 259. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000

theorem degreeSevenStageSevenScaledRows200To299Chunk005_parts :
    degreeSevenStageSevenScaledRows200To299Chunk005 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005.length =
      7 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005).length =
      0 := by
  rfl

end

end TraceEuclidean
