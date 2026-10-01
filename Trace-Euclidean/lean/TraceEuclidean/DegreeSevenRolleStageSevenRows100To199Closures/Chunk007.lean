import TraceEuclidean.DegreeSevenRolleStageSixPiecewiseRows100To199Chunks.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenRows100To199Chunks.Chunk007

/-! Stage Seven classification closure for Stage Five rows 170 through 179. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesRows100To199Chunk007 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewiseRows100To199Chunk007

def degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk007 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledRows100To199Chunk007
    degreeSevenStageSevenMultipleRootRows100To199Chunk007
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk007

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenRows100To199Chunk007_keyLists_eq :
    degreeSevenStageSixPrefixesRows100To199Chunk007 =
      degreeSevenStageSevenClassificationsRows100To199Chunk007.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesRows100To199Chunk007,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewiseRows100To199Chunk007,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsRows100To199Chunk007,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenRows100To199Chunk007_keyFinsets_eq :
    degreeSevenStageSixPrefixesRows100To199Chunk007.toFinset =
      degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk007.toFinset := by
  rw [degreeSevenStageSevenRows100To199Chunk007_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesRows100To199Chunk007,
    degreeSevenStageSevenScaledRows100To199Chunk007,
    degreeSevenStageSevenMultipleRootRows100To199Chunk007,
    degreeSevenStageSevenScaledCriticalSignRows100To199Chunk007] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsRows100To199Chunk007)

end

end TraceEuclidean
