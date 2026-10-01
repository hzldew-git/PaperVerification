import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk002

/-! Stage Seven classification closure for Stage Five rows 20 through 29. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk002 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk002

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk002 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk002
    degreeSevenStageSevenMultipleRootPrefix100Chunk002
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk002_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk002 =
      degreeSevenStageSevenClassificationsPrefix100Chunk002.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk002,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk002,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk002,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk002_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk002.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk002.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk002_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk002,
    degreeSevenStageSevenScaledPrefix100Chunk002,
    degreeSevenStageSevenMultipleRootPrefix100Chunk002,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk002] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk002)

end

end TraceEuclidean
