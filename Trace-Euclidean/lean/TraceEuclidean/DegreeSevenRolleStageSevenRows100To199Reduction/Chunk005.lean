import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk005Part000

/-! Candidate reduction for Stage Five rows 150 through 159. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005Part000

theorem degreeSevenStageSevenScaledRows100To199Chunk005_parts :
    degreeSevenStageSevenScaledRows100To199Chunk005 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005.Forall
      (fun certificate => certificate.check = true) := by
  exact degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005Part000_valid

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005.length =
      25 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005).length =
      14 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk005).length =
      0 := by
  rfl

end

end TraceEuclidean
