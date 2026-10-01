import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk009
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part009
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part010
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part011
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part012
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part013
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part014
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part015
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part016
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199ReductionParts.Chunk009Part017

/-! Candidate reduction for Stage Five rows 190 through 199. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009 :
    List DegreeSevenFinalEntryCertificate :=
  degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part000 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part001 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part002 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part003 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part004 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part005 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part006 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part007 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part008 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part009 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part010 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part011 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part012 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part013 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part014 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part015 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part016 ++
    (degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part017)))))))))))))))))

theorem degreeSevenStageSevenScaledRows100To199Chunk009_parts :
    degreeSevenStageSevenScaledRows100To199Chunk009 =
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009.map
        DegreeSevenFinalEntryCertificate.entry := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009.Forall
      (fun certificate => certificate.check = true) := by
  exact List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part000_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part001_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part002_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part003_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part004_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part005_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part006_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part007_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part008_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part009_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part010_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part011_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part012_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part013_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part014_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part015_valid,
    List.forall_append.mpr ⟨degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part016_valid,
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009Part017_valid⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009.length =
      450 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009).length =
      202 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk009).length =
      7 := by
  rfl

end

end TraceEuclidean
