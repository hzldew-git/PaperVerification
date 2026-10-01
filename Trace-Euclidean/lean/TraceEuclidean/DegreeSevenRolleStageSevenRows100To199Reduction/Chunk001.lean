import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk001Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk001Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk001Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk001Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk001Part004

/-! Candidate reduction for Stage Five rows 110 through 119. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part004))))

theorem degreeSevenStageSevenScaledRows100To199Chunk001_parts :
    degreeSevenStageSevenScaledRows100To199Chunk001 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part003_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001Part004_valid⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001.length =
      118 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001).length =
      46 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk001).length =
      0 := by
  rfl

end

end TraceEuclidean
