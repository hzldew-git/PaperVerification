import TraceEuclidean.DegreeSevenRolleStageSixPiecewiseRows200To299Chunks.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenRows200To299Chunks.Chunk000

/-! Stage Seven classification closure for Stage Five rows 200 through 209. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows200To299Chunk000 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewiseRows200To299Chunk000

def degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk000 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows200To299Chunk000
    degreeSevenStageSevenMultipleRootRows200To299Chunk000
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk000

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenRows200To299Chunk000_keyLists_eq :
    degreeSevenStageSixPrefixesRows200To299Chunk000 =
      degreeSevenStageSevenClassificationsRows200To299Chunk000.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesRows200To299Chunk000,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewiseRows200To299Chunk000,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsRows200To299Chunk000,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenRows200To299Chunk000_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows200To299Chunk000.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk000.toFinset := by
  rw [degreeSevenStageSevenRows200To299Chunk000_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows200To299Chunk000,
    degreeSevenStageSevenScaledRows200To299Chunk000,
    degreeSevenStageSevenMultipleRootRows200To299Chunk000,
    degreeSevenStageSevenScaledCriticalSignRows200To299Chunk000] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows200To299Chunk000)

end

end TraceEuclidean
