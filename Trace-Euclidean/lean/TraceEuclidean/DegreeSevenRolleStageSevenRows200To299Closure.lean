import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Closures.Chunk009

/-!
# Classification bridge for the degree-seven Stage Five rows 200 through 299

The ten chunk theorems classify every nonconstant coefficient prefix produced
by the exact piecewise Stage Six certificates for rows 200 through 299. The
ordered classification list avoids a monolithic finite-set computation.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows200To299 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixesRows200To299Chunk000 ++
    degreeSevenStageSixPrefixesRows200To299Chunk001 ++
    degreeSevenStageSixPrefixesRows200To299Chunk002 ++
    degreeSevenStageSixPrefixesRows200To299Chunk003 ++
    degreeSevenStageSixPrefixesRows200To299Chunk004 ++
    degreeSevenStageSixPrefixesRows200To299Chunk005 ++
    degreeSevenStageSixPrefixesRows200To299Chunk006 ++
    degreeSevenStageSixPrefixesRows200To299Chunk007 ++
    degreeSevenStageSixPrefixesRows200To299Chunk008 ++
    degreeSevenStageSixPrefixesRows200To299Chunk009

def degreeSevenStageSevenClassificationsRows200To299 :
    List DegreeSevenStageSevenClassification :=
  degreeSevenStageSevenClassificationsRows200To299Chunk000 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk001 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk002 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk003 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk004 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk005 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk006 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk007 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk008 ++
    degreeSevenStageSevenClassificationsRows200To299Chunk009

def degreeSevenStageSevenScaledRows200To299 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows200To299

def degreeSevenStageSevenMultipleRootRows200To299 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows200To299

def degreeSevenStageSevenScaledCriticalSignRows200To299 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows200To299

def degreeSevenStageSevenCriticalSignRows200To299 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows200To299.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

def degreeSevenStageSevenClassifiedPrefixesRows200To299 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows200To299
    degreeSevenStageSevenMultipleRootRows200To299
    degreeSevenStageSevenScaledCriticalSignRows200To299

theorem degreeSevenStageSevenClassificationsRows200To299_valid :
    degreeSevenStageSevenClassificationsRows200To299.Forall
      DegreeSevenStageSevenClassification.Valid := by
  unfold degreeSevenStageSevenClassificationsRows200To299
  exact List.forall_append.mpr ⟨
    List.forall_append.mpr ⟨
      List.forall_append.mpr ⟨
        List.forall_append.mpr ⟨
          List.forall_append.mpr ⟨
            List.forall_append.mpr ⟨
              List.forall_append.mpr ⟨
                List.forall_append.mpr ⟨
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenClassificationsRows200To299Chunk000_valid,
                    degreeSevenStageSevenClassificationsRows200To299Chunk001_valid⟩,
                  degreeSevenStageSevenClassificationsRows200To299Chunk002_valid⟩,
                degreeSevenStageSevenClassificationsRows200To299Chunk003_valid⟩,
              degreeSevenStageSevenClassificationsRows200To299Chunk004_valid⟩,
            degreeSevenStageSevenClassificationsRows200To299Chunk005_valid⟩,
          degreeSevenStageSevenClassificationsRows200To299Chunk006_valid⟩,
        degreeSevenStageSevenClassificationsRows200To299Chunk007_valid⟩,
      degreeSevenStageSevenClassificationsRows200To299Chunk008_valid⟩,
    degreeSevenStageSevenClassificationsRows200To299Chunk009_valid⟩

theorem degreeSevenStageSevenScaledRows200To299_valid :
    degreeSevenStageSevenScaledRows200To299.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact DegreeSevenStageSevenClassification.scaledEntries_forall_valid
    degreeSevenStageSevenClassificationsRows200To299_valid

theorem degreeSevenStageSevenMultipleRootRows200To299_valid :
    degreeSevenStageSevenMultipleRootRows200To299.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  exact DegreeSevenStageSevenClassification.multipleRoots_forall_valid
    degreeSevenStageSevenClassificationsRows200To299_valid

theorem degreeSevenStageSevenScaledCriticalSignRows200To299_valid :
    degreeSevenStageSevenScaledCriticalSignRows200To299.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact DegreeSevenStageSevenClassification.criticalSigns_forall_valid
    degreeSevenStageSevenClassificationsRows200To299_valid

theorem degreeSevenStageSevenCriticalSignRows200To299_valid :
    degreeSevenStageSevenCriticalSignRows200To299.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows200To299, List.forall_map_iff]
  exact degreeSevenStageSevenScaledCriticalSignRows200To299_valid

theorem degreeSevenStageSevenClassificationsRows200To299_count :
    degreeSevenStageSevenClassificationsRows200To299.length = 3170 := by
  rfl

theorem degreeSevenStageSevenScaledRows200To299_count :
    degreeSevenStageSevenScaledRows200To299.length = 2725 := by
  rfl

theorem degreeSevenStageSevenMultipleRootRows200To299_count :
    degreeSevenStageSevenMultipleRootRows200To299.length = 72 := by
  rfl

theorem degreeSevenStageSevenCriticalSignRows200To299_count :
    degreeSevenStageSevenScaledCriticalSignRows200To299.length = 373 := by
  rfl

theorem degreeSevenStageSevenClassifiedPrefixesRows200To299_count :
    degreeSevenStageSevenClassifiedPrefixesRows200To299.length = 3170 := by
  rfl

theorem degreeSevenStageSevenRows200To299_keyLists_eq :
    degreeSevenStageSixPrefixesRows200To299 =
      degreeSevenStageSevenClassificationsRows200To299.map
        DegreeSevenStageSevenClassification.toPrefix := by
  simp only [degreeSevenStageSixPrefixesRows200To299,
    degreeSevenStageSevenClassificationsRows200To299, List.map_append]
  rw [degreeSevenStageSevenRows200To299Chunk000_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk001_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk002_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk003_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk004_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk005_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk006_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk007_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk008_keyLists_eq,
    degreeSevenStageSevenRows200To299Chunk009_keyLists_eq]

theorem degreeSevenStageSevenRows200To299_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows200To299.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows200To299.toFinset := by
  rw [degreeSevenStageSevenRows200To299_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows200To299,
    degreeSevenStageSevenScaledRows200To299,
    degreeSevenStageSevenMultipleRootRows200To299,
    degreeSevenStageSevenScaledCriticalSignRows200To299] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows200To299)

/-- Every Hunter candidate matching one of the certified rows 200 through 299 has
its constant coefficient in the exact final finite set. -/
theorem degreeSevenStageSevenRows200To299_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows200To299)
    (ha6 : entry.a6 = f.coeff 6)
    (ha5 : entry.a5 = f.coeff 5)
    (ha4 : entry.a4 = f.coeff 4)
    (ha3 : entry.a3 = f.coeff 3)
    (ha2 : entry.a2 = f.coeff 2)
    (ha1 : entry.a1 = f.coeff 1) :
    f.coeff 0 ∈ entry.toEntry.a0Candidates := by
  apply degreeSeven_minimumHunterCandidate_a0_mem_of_stageSeven
    h entry.toEntry
  · exact (List.forall_iff_forall_mem.mp
      degreeSevenStageSevenScaledRows200To299_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
