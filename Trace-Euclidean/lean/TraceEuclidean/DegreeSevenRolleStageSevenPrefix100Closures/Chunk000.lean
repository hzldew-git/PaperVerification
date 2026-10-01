import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk000
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk000

/-! Stage Seven classification closure for Stage Five rows 0 through 9. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk000 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk000

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk000 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk000
    degreeSevenStageSevenMultipleRootPrefix100Chunk000
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk000_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk000 =
      degreeSevenStageSevenClassificationsPrefix100Chunk000.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk000,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk000,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk000,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk000_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk000.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk000.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk000_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk000,
    degreeSevenStageSevenScaledPrefix100Chunk000,
    degreeSevenStageSevenMultipleRootPrefix100Chunk000,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk000] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk000)

end

end TraceEuclidean
