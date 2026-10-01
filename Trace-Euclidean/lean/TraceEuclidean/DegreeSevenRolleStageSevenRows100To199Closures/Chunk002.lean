import TraceEuclidean.DegreeSevenRolleStageSixPiecewiseRows100To199Chunks.Chunk002
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk002

/-! Stage Seven classification closure for Stage Five rows 120 through 129. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows100To199Chunk002 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewiseRows100To199Chunk002

def degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk002 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows100To199Chunk002
    degreeSevenStageSevenMultipleRootRows100To199Chunk002
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenRows100To199Chunk002_keyLists_eq :
    degreeSevenStageSixPrefixesRows100To199Chunk002 =
      degreeSevenStageSevenClassificationsRows100To199Chunk002.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesRows100To199Chunk002,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewiseRows100To199Chunk002,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsRows100To199Chunk002,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenRows100To199Chunk002_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows100To199Chunk002.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk002.toFinset := by
  rw [degreeSevenStageSevenRows100To199Chunk002_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk002,
    degreeSevenStageSevenScaledRows100To199Chunk002,
    degreeSevenStageSevenMultipleRootRows100To199Chunk002,
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk002] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows100To199Chunk002)

end

end TraceEuclidean
