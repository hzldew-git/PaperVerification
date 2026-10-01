import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk001
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk001

/-! Stage Seven classification closure for Stage Five rows 10 through 19. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk001 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk001

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk001 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk001
    degreeSevenStageSevenMultipleRootPrefix100Chunk001
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk001_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk001 =
      degreeSevenStageSevenClassificationsPrefix100Chunk001.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk001,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk001,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk001,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk001_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk001.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk001.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk001_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk001,
    degreeSevenStageSevenScaledPrefix100Chunk001,
    degreeSevenStageSevenMultipleRootPrefix100Chunk001,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk001] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk001)

end

end TraceEuclidean
