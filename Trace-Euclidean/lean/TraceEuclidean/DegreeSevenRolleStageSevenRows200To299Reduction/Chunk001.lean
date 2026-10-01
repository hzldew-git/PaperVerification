import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk001Part000

/-! Candidate reduction for Stage Five rows 210 through 219. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000

theorem degreeSevenStageSevenScaledRows200To299Chunk001_parts :
    degreeSevenStageSevenScaledRows200To299Chunk001 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001.length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001).length =
      1 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001).length =
      0 := by
  rfl

end

end TraceEuclidean
