import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk003

/-! Stage Seven classification closure for Stage Five rows 30 through 39. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk003 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk003

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk003 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk003
    degreeSevenStageSevenMultipleRootPrefix100Chunk003
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk003_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk003 =
      degreeSevenStageSevenClassificationsPrefix100Chunk003.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk003,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk003,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk003,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk003_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk003.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk003.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk003_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk003,
    degreeSevenStageSevenScaledPrefix100Chunk003,
    degreeSevenStageSevenMultipleRootPrefix100Chunk003,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk003] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk003)

end

end TraceEuclidean
