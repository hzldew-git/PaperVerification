import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk009
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299ReductionParts.Chunk009Part000

/-! Candidate reduction for Stage Five rows 290 through 299. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000

theorem degreeSevenStageSevenScaledRows200To299Chunk009_parts :
    degreeSevenStageSevenScaledRows200To299Chunk009 =
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009.length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009).length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009).length =
      0 := by
  rfl

end

end TraceEuclidean
