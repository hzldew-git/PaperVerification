import TraceEuclidean.DegreeSevenRolleStageSixPiecewisePrefix100Chunks.Chunk004
import TraceEuclidean.DegreeSevenRolleStageSevenPrefixBridge
import TraceEuclidean.DegreeSevenRolleStageSevenPrefix100Chunks.Chunk004

/-! Stage Seven classification closure for Stage Five rows 40 through 49. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSixPrefixesPrefix100Chunk004 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSixPrefixes
    degreeSevenStageSixPiecewisePrefix100Chunk004

def degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk004 :
    List DegreeSevenStageSevenPrefix :=
  degreeSevenStageSevenClassifiedPrefixes
    degreeSevenStageSevenScaledPrefix100Chunk004
    degreeSevenStageSevenMultipleRootPrefix100Chunk004
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004

set_option maxHeartbeats 0 in
-- Cleared-denominator integer reduction links Stage Six to Stage Seven.
theorem degreeSevenStageSevenPrefix100Chunk004_keyLists_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk004 =
      degreeSevenStageSevenClassificationsPrefix100Chunk004.map
        DegreeSevenStageSevenClassification.toPrefix := by
  norm_num (config := { maxSteps := 2000000 })
    [degreeSevenStageSixPrefixesPrefix100Chunk004,
    degreeSevenStageSixPrefixes,
    degreeSevenStageSixPiecewisePrefix100Chunk004,
    DegreeSevenStageSixScaledFamily.toFamily,
    DegreeSevenStageSixFamily.a2Candidates,
    DegreeSevenStageSixScaledFamily.scaledA1Candidates,
    integerIccList, Int.toNat_of_nonpos, List.range_succ,
    degreeSevenStageSevenClassificationsPrefix100Chunk004,
    DegreeSevenStageSevenClassification.toPrefix,
    DegreeSevenStageSevenPrefix.ofScaledEntry,
    DegreeSevenStageSevenPrefix.ofMultipleRootWitness,
    DegreeSevenStageSevenPrefix.ofScaledCriticalSignWitness]
  simp (config := { dsimp := true, maxSteps := 2000000 })
    [Int.toNat, List.range_succ] <;> rfl

theorem degreeSevenStageSevenPrefix100Chunk004_keyFinsets_eq :
    degreeSevenStageSixPrefixesPrefix100Chunk004.toFinset =
      degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk004.toFinset := by
  rw [degreeSevenStageSevenPrefix100Chunk004_keyLists_eq]
  simpa [degreeSevenStageSevenClassifiedPrefixesPrefix100Chunk004,
    degreeSevenStageSevenScaledPrefix100Chunk004,
    degreeSevenStageSevenMultipleRootPrefix100Chunk004,
    degreeSevenStageSevenScaledCriticalSignPrefix100Chunk004] using
    (degreeSevenStageSevenClassification_prefixes_toFinset
      degreeSevenStageSevenClassificationsPrefix100Chunk004)

end

end TraceEuclidean
