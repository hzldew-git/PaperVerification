import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk007
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk007

/-! Stage Seven classification closure for Stage Five rows 70 through 79. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk007 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk007

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk007 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk007
    degreeSevenStageSevenMultipleRootPrefix100Chunk007
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk007

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk007_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk007 =
      degreeSevenStageSevenClassificationsPrefix100Chunk007.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk007,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk007,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk007,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk007_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk007.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk007.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk007_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk007,
    degreeSevenStageSevenScaledPrefix100Chunk007,
    degreeSevenStageSevenMultipleRootPrefix100Chunk007,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk007] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk007)

end

end TraceEuclidean
