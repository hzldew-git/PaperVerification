import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk008
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk008

/-! Stage Seven classification closure for Stage Five rows 80 through 89. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk008 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk008

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk008 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk008
    degreeSevenStageSevenMultipleRootPrefix100Chunk008
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk008

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk008_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk008 =
      degreeSevenStageSevenClassificationsPrefix100Chunk008.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk008,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk008,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk008,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk008_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk008.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk008.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk008_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk008,
    degreeSevenStageSevenScaledPrefix100Chunk008,
    degreeSevenStageSevenMultipleRootPrefix100Chunk008,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk008] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk008)

end

end TraceEuclidean
