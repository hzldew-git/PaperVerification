import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk009
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk009

/-! Stage Seven classification closure for Stage Five rows 90 through 99. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk009 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk009

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk009 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk009
    degreeSevenStageSevenMultipleRootPrefix100Chunk009
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk009

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk009_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk009 =
      degreeSevenStageSevenClassificationsPrefix100Chunk009.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk009,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk009,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk009,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk009_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk009.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk009.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk009_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk009,
    degreeSevenStageSevenScaledPrefix100Chunk009,
    degreeSevenStageSevenMultipleRootPrefix100Chunk009,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk009] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk009)

end

end TraceEuclidean
