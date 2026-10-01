import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk005
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Closures.Chunk009

/-!
# Classification bridge for the degree-seven Stage Five rows 100 through 199

The ten chunk theorems classify every nonconstant coefficient prefix produced
by the exact piecewise Stage Six certificates for rows 100 through 199. The
ordered classification list avoids a monolithic finite-set computation.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows100To199 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixesRows100To199Chunk000 ++
    degreeSevenStageSixPrefixesRows100To199Chunk001 ++
    degreeSevenStageSixPrefixesRows100To199Chunk002 ++
    degreeSevenStageSixPrefixesRows100To199Chunk003 ++
    degreeSevenStageSixPrefixesRows100To199Chunk004 ++
    degreeSevenStageSixPrefixesRows100To199Chunk005 ++
    degreeSevenStageSixPrefixesRows100To199Chunk006 ++
    degreeSevenStageSixPrefixesRows100To199Chunk007 ++
    degreeSevenStageSixPrefixesRows100To199Chunk008 ++
    degreeSevenStageSixPrefixesRows100To199Chunk009

def degreeSevenStageSevenClassificationsRows100To199 :
    List DegreeSevenStageSevenClassification :=
  degreeSevenStageSevenClassificationsRows100To199Chunk000 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk001 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk002 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk003 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk004 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk005 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk006 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk007 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk008 ++
    degreeSevenStageSevenClassificationsRows100To199Chunk009

def degreeSevenStageSevenScaledRows100To199 :
    List DegreeSevenStageSevenScaledEntry :=
  DegreeSevenStageSevenClassification.scaledEntries
    degreeSevenStageSevenClassificationsRows100To199

def degreeSevenStageSevenMultipleRootRows100To199 :
    List DegreeSevenStageSevenMultipleRootWitness :=
  DegreeSevenStageSevenClassification.multipleRoots
    degreeSevenStageSevenClassificationsRows100To199

def degreeSevenStageSevenScaledCriticalSignRows100To199 :
    List DegreeSevenStageSevenScaledCriticalSignWitness :=
  DegreeSevenStageSevenClassification.criticalSigns
    degreeSevenStageSevenClassificationsRows100To199

def degreeSevenStageSevenCriticalSignRows100To199 :
    List DegreeSevenStageSevenCriticalSignWitness :=
  degreeSevenStageSevenScaledCriticalSignRows100To199.map
    DegreeSevenStageSevenScaledCriticalSignWitness.toWitness

def degreeSevenStageSevenClassifiedPrefixesRows100To199 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows100To199
    degreeSevenStageSevenMultipleRootRows100To199
    degreeSevenStageSevenScaledCriticalSignRows100To199

theorem degreeSevenStageSevenClassificationsRows100To199_valid :
    degreeSevenStageSevenClassificationsRows100To199.Forall
      DegreeSevenStageSevenClassification.Valid := by
  unfold degreeSevenStageSevenClassificationsRows100To199
  exact List.forall_append.mpr ⟨
    List.forall_append.mpr ⟨
      List.forall_append.mpr ⟨
        List.forall_append.mpr ⟨
          List.forall_append.mpr ⟨
            List.forall_append.mpr ⟨
              List.forall_append.mpr ⟨
                List.forall_append.mpr ⟨
                  List.forall_append.mpr ⟨
                    degreeSevenStageSevenClassificationsRows100To199Chunk000_valid,
                    degreeSevenStageSevenClassificationsRows100To199Chunk001_valid⟩,
                  degreeSevenStageSevenClassificationsRows100To199Chunk002_valid⟩,
                degreeSevenStageSevenClassificationsRows100To199Chunk003_valid⟩,
              degreeSevenStageSevenClassificationsRows100To199Chunk004_valid⟩,
            degreeSevenStageSevenClassificationsRows100To199Chunk005_valid⟩,
          degreeSevenStageSevenClassificationsRows100To199Chunk006_valid⟩,
        degreeSevenStageSevenClassificationsRows100To199Chunk007_valid⟩,
      degreeSevenStageSevenClassificationsRows100To199Chunk008_valid⟩,
    degreeSevenStageSevenClassificationsRows100To199Chunk009_valid⟩

theorem degreeSevenStageSevenScaledRows100To199_valid :
    degreeSevenStageSevenScaledRows100To199.Forall
      (fun entry => entry.toEntry.Valid) := by
  exact DegreeSevenStageSevenClassification.scaledEntries_forall_valid
    degreeSevenStageSevenClassificationsRows100To199_valid

theorem degreeSevenStageSevenMultipleRootRows100To199_valid :
    degreeSevenStageSevenMultipleRootRows100To199.Forall
      DegreeSevenStageSevenMultipleRootWitness.Valid := by
  exact DegreeSevenStageSevenClassification.multipleRoots_forall_valid
    degreeSevenStageSevenClassificationsRows100To199_valid

theorem degreeSevenStageSevenScaledCriticalSignRows100To199_valid :
    degreeSevenStageSevenScaledCriticalSignRows100To199.Forall
      (fun witness => witness.toWitness.Valid) := by
  exact DegreeSevenStageSevenClassification.criticalSigns_forall_valid
    degreeSevenStageSevenClassificationsRows100To199_valid

theorem degreeSevenStageSevenCriticalSignRows100To199_valid :
    degreeSevenStageSevenCriticalSignRows100To199.Forall
      DegreeSevenStageSevenCriticalSignWitness.Valid := by
  rw [degreeSevenStageSevenCriticalSignRows100To199, List.forall_map_iff]
  exact degreeSevenStageSevenScaledCriticalSignRows100To199_valid

theorem degreeSevenStageSevenClassificationsRows100To199_count :
    degreeSevenStageSevenClassificationsRows100To199.length = 1805 := by
  rfl

theorem degreeSevenStageSevenScaledRows100To199_count :
    degreeSevenStageSevenScaledRows100To199.length = 1369 := by
  rfl

theorem degreeSevenStageSevenMultipleRootRows100To199_count :
    degreeSevenStageSevenMultipleRootRows100To199.length = 72 := by
  rfl

theorem degreeSevenStageSevenCriticalSignRows100To199_count :
    degreeSevenStageSevenScaledCriticalSignRows100To199.length = 364 := by
  rfl

theorem degreeSevenStageSevenClassifiedPrefixesRows100To199_count :
    degreeSevenStageSevenClassifiedPrefixesRows100To199.length = 1805 := by
  rfl

theorem degreeSevenStageSevenRows100To199_keyLists_eq :
    degreeSevenStageSixPrefixesRows100To199 =
      degreeSevenStageSevenClassificationsRows100To199.map
        DegreeSevenStageSevenClassification.toPrefix := by
  simp only [degreeSevenStageSixPrefixesRows100To199,
    degreeSevenStageSevenClassificationsRows100To199, List.map_append]
  rw [degreeSevenStageSevenRows100To199Chunk000_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk001_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk002_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk003_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk004_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk005_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk006_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk007_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk008_keyLists_eq,
    degreeSevenStageSevenRows100To199Chunk009_keyLists_eq]

theorem degreeSevenStageSevenRows100To199_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows100To199.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows100To199.toFinset := by
  rw [degreeSevenStageSevenRows100To199_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows100To199,
    degreeSevenStageSevenScaledRows100To199,
    degreeSevenStageSevenMultipleRootRows100To199,
    degreeSevenStageSevenScaledCriticalSignRows100To199] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows100To199)

/-- Every Hunter candidate matching one of the certified rows 100 through 199 has
its constant coefficient in the exact final finite set. -/
theorem degreeSevenStageSevenRows100To199_a0_mem
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    (entry : DegreeSevenStageSevenScaledEntry)
    (hentry : entry ∈ degreeSevenStageSevenScaledRows100To199)
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
      degreeSevenStageSevenScaledRows100To199_valid) entry hentry
  · exact ha6
  · exact ha5
  · exact ha4
  · exact ha3
  · exact ha2
  · exact ha1

end

end TraceEuclidean
