import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk006
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk006

/-! Stage Seven classification closure for Stage Five rows 60 through 69. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk006 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk006

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk006 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk006
    degreeSevenStageSevenMultipleRootPrefix100Chunk006
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk006

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk006_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk006 =
      degreeSevenStageSevenClassificationsPrefix100Chunk006.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk006,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk006,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk006,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk006_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk006.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk006.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk006_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk006,
    degreeSevenStageSevenScaledPrefix100Chunk006,
    degreeSevenStageSevenMultipleRootPrefix100Chunk006,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk006] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk006)

end

end TraceEuclidean
