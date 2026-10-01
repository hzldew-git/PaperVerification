import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk003Part009

/-! Candidate reduction for Stage Five rows 130 through 139. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part008 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009)))))))))

theorem degreeSevenStageSevenScaledRows100To199Chunk003_parts :
    degreeSevenStageSevenScaledRows100To199Chunk003 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part007_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part008_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003.length =
      229 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003).length =
      90 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003).length =
      0 := by
  rfl

end

end TraceEuclidean
