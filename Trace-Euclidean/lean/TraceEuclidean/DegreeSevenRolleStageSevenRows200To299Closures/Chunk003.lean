import TraceEuclidean.DegreeSevenRolleStageSixPiecewiseRows200To299Chunks.Chunk003
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk003

/-! Stage Seven classification closure for Stage Five rows 230 through 239. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows200To299Chunk003 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewiseRows200To299Chunk003

def degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk003 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows200To299Chunk003
    degreeSevenStageSevenMultipleRootRows200To299Chunk003
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk003

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenRows200To299Chunk003_keyLists_eq :
    degreeSevenStageSixPrefixesRows200To299Chunk003 =
      degreeSevenStageSevenClassificationsRows200To299Chunk003.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesRows200To299Chunk003,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewiseRows200To299Chunk003,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsRows200To299Chunk003,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenRows200To299Chunk003_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows200To299Chunk003.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk003.toFinset := by
  rw [degreeSevenStageSevenRows200To299Chunk003_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk003,
    degreeSevenStageSevenScaledRows200To299Chunk003,
    degreeSevenStageSevenMultipleRootRows200To299Chunk003,
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk003] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows200To299Chunk003)

end

end TraceEuclidean
