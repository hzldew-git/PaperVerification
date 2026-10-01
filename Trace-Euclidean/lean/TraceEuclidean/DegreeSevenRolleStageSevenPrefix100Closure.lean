import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Closures.Chunk009

/-!
# Classification bridge for the first 100 degree-seven Stage Five rows

The ten chunk theorems classify every nonconstant coefficient prefix produced
by the exact piecewise Stage Six certificates for the first 100 rows. The
ordered classification list avoids a monolithic finite-set computation.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixesPrefix100Chunk000 ++
    degreeSevenStageSixPrefixesPrefix100Chunk001 ++
    degreeSevenStageSixPrefixesPrefix100Chunk002 ++
    degreeSevenStageSixPrefixesPrefix100Chunk003 ++
    degreeSevenStageSixPrefixesPrefix100Chunk004 ++
    degreeSevenStageSixPrefixesPrefix100Chunk005 ++
    degreeSevenStageSixPrefixesPrefix100Chunk006 ++
    degreeSevenStageSixPrefixesPrefix100Chunk007 ++
    degreeSevenStageSixPrefixesPrefix100Chunk008 ++
    degreeSevenStageSixPrefixesPrefix100Chunk009

def degreeSevenStageSevenClassificationsPrefix100 :
    List DegreeSevenStageSevenClassification :=
  degreeSevenStageSevenClassificationsPrefix100Chunk000 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk001 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk002 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk003 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk004 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk005 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk006 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk007 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk008 ++
    degreeSevenStageSevenClassificationsPrefix100Chunk009

def degreeSevenStageSevenScaledPrefix100 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsPrefix100

def degreeSevenStageSevenMultipleRootPrefix100 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsPrefix100

def degreeSevenStageSevenScaledCriticalSignPrefix100 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsPrefix100

def degreeSevenStageSevenCriticalSignPrefix100 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignPrefix100.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

def degreeSevenStageSevenClassifiedPrefixesPrefix100 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100
    degreeSevenStageSevenMultipleRootPrefix100
    degreeSevenStageSevenScaledCriticalSignPrefix100

theorem degreeSevenStageSevenClassificationsPrefix100_valid :
    degreeSevenStageSevenClassificationsPrefix100.Forall
      DegreeSevenStageSevenClassification.Valid := by
  unfold degreeSevenStageSevenClassificationsPrefix100
  exact List.forall_append.mpr ⟨
    List.forall_append.mpr ⟨
      List.forall_append.mpr ⟨
        List.forall_append.mpr ⟨
          List.forall_append.mpr ⟨
            List.forall_append.mpr ⟨
              List.forall_append.mpr ⟨
                List.forall_append.mpr ⟨
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenClassificationsPrefix100Chunk000_valid,
                    degreeSevenStageSevenClassificationsPrefix100Chunk001_valid⟩,
                  degreeSevenStageSevenClassificationsPrefix100Chunk002_valid⟩,
                degreeSevenStageSevenClassificationsPrefix100Chunk003_valid⟩,
              degreeSevenStageSevenClassificationsPrefix100Chunk004_valid⟩,
            degreeSevenStageSevenClassificationsPrefix100Chunk005_valid⟩,
          degreeSevenStageSevenClassificationsPrefix100Chunk006_valid⟩,
        degreeSevenStageSevenClassificationsPrefix100Chunk007_valid⟩,
      degreeSevenStageSevenClassificationsPrefix100Chunk008_valid⟩,
    degreeSevenStageSevenClassificationsPrefix100Chunk009_valid⟩

theorem degreeSevenStageSevenScaledPrefix100_valid :
    degreeSevenStageSevenScaledPrefix100.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact DegreeSevenStageSevenClassification.scaledEntries_forall_valid
    degreeSevenStageSevenClassificationsPrefix100_valid

theorem degreeSevenStageSevenMultipleRootPrefix100_valid :
    degreeSevenStageSevenMultipleRootPrefix100.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  exact DegreeSevenStageSevenClassification.multipleRoots_forall_valid
    degreeSevenStageSevenClassificationsPrefix100_valid

theorem degreeSevenStageSevenScaledCriticalSignPrefix100_valid :
    degreeSevenStageSevenScaledCriticalSignPrefix100.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact DegreeSevenStageSevenClassification.criticalSigns_forall_valid
    degreeSevenStageSevenClassificationsPrefix100_valid

theorem degreeSevenStageSevenCriticalSignPrefix100_valid :
    degreeSevenStageSevenCriticalSignPrefix100.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignPrefix100, List.forall_map_iff]
  exact degreeSevenStageSevenScaledCriticalSignPrefix100_valid

theorem degreeSevenStageSevenClassificationsPrefix100_count :
    degreeSevenStageSevenClassificationsPrefix100.length = 476 := by
  rfl

theorem degreeSevenStageSevenScaledPrefix100_count :
    degreeSevenStageSevenScaledPrefix100.length = 222 := by
  rfl

theorem degreeSevenStageSevenMultipleRootPrefix100_count :
    degreeSevenStageSevenMultipleRootPrefix100.length = 49 := by
  rfl

theorem degreeSevenStageSevenCriticalSignPrefix100_count :
    degreeSevenStageSevenScaledCriticalSignPrefix100.length = 205 := by
  rfl

theorem degreeSevenStageSevenClassifiedPrefixesPrefix100_count :
    degreeSevenStageSevenClassifiedPrefixesPrefix100.length = 476 := by
  rfl

theorem degreeSevenStageSevenPrefix100_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100 =
      degreeSevenStageSevenClassificationsPrefix100.map
        DegreeSevenStageSevenClassification.toPrefix := by
  simp only [degreeSevenStageSixPrefixesPrefix100,
    degreeSevenStageSevenClassificationsPrefix100, List.map_append]
  rw [degreeSevenStageSevenPrefix100Chunk000_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk001_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk002_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk003_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk004_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk005_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk006_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk007_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk008_keyLists_eq,
    degreeSevenStageSevenPrefix100Chunk009_keyLists_eq]

theorem degreeSevenStageSevenPrefix100_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100.toFinset := by
  rw [degreeSevenStageSevenPrefix100_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100,
    degreeSevenStageSevenScaledPrefix100,
    degreeSevenStageSevenMultipleRootPrefix100,
    degreeSevenStageSevenScaledCriticalSignPrefix100] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100)

/-- Every Hunter candidate matching one of the first 100 certified rows has
its constant coefficient in the exact final finite set. -/
theorem degreeSevenStageSevenPrefix100_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledPrefix100)
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
      degreeSevenStageSevenScaledPrefix100_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
