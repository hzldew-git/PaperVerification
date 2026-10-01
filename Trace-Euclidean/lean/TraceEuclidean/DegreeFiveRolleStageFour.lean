import TraceEuclidean.DegreeFiveRolleStageThree
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk000
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk001
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk002
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk003
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk004
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk005
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk006
import TraceEuclidean.DegreeFiveRolleStageFourCertificates.Chunk007

/-! Complete generated fourth-stage frontier for the quintic Rolle search. -/

namespace TraceEuclidean

def degreeFiveStageFourEntries :
    List DegreeFiveStageFourEntry :=
  degreeFiveStageFourEntriesChunk000 ++
    degreeFiveStageFourEntriesChunk001 ++
    degreeFiveStageFourEntriesChunk002 ++
    degreeFiveStageFourEntriesChunk003 ++
    degreeFiveStageFourEntriesChunk004 ++
    degreeFiveStageFourEntriesChunk005 ++
    degreeFiveStageFourEntriesChunk006 ++
    degreeFiveStageFourEntriesChunk007

/-- The exact coefficient ranges attached to all 187 certified cubic rows. -/
def degreeFiveStageFourExpectedRanges :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  degreeFiveStageFourExpectedRangesChunk000 ++
    degreeFiveStageFourExpectedRangesChunk001 ++
    degreeFiveStageFourExpectedRangesChunk002 ++
    degreeFiveStageFourExpectedRangesChunk003 ++
    degreeFiveStageFourExpectedRangesChunk004 ++
    degreeFiveStageFourExpectedRangesChunk005 ++
    degreeFiveStageFourExpectedRangesChunk006 ++
    degreeFiveStageFourExpectedRangesChunk007

/-- Coefficient triples represented by the certified cubic rows. -/
def degreeFiveStageFourTopTriples : List (ℤ × ℤ × ℤ) :=
  [
    ((-2 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (15 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (16 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (17 : ℤ)),
    ((-2 : ℤ), (-5 : ℤ), (18 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (12 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (13 : ℤ)),
    ((-2 : ℤ), (-4 : ℤ), (14 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (9 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (10 : ℤ)),
    ((-2 : ℤ), (-3 : ℤ), (11 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (6 : ℤ)),
    ((-2 : ℤ), (-2 : ℤ), (7 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (0 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (3 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (4 : ℤ)),
    ((-2 : ℤ), (-1 : ℤ), (5 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (1 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((-2 : ℤ), (1 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-6 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-5 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (12 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (13 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-4 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (9 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (10 : ℤ)),
    ((-1 : ℤ), (-5 : ℤ), (11 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-3 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (6 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (7 : ℤ)),
    ((-1 : ℤ), (-4 : ℤ), (8 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (-2 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (4 : ℤ)),
    ((-1 : ℤ), (-3 : ℤ), (5 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (2 : ℤ)),
    ((-1 : ℤ), (-2 : ℤ), (3 : ℤ)),
    ((-1 : ℤ), (-1 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-1 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-9 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-8 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (8 : ℤ)),
    ((0 : ℤ), (-6 : ℤ), (9 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-7 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-6 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-5 : ℤ), (7 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-5 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-4 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-4 : ℤ), (5 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-1 : ℤ), (0 : ℤ))
  ]

/-- The four third-stage triples whose cubic has a multiple root. -/
def degreeFiveStageFourRejectedTriples : List (ℤ × ℤ × ℤ) :=
  [
    ((-2 : ℤ), (-2 : ℤ), (8 : ℤ)),
    ((-2 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((-1 : ℤ), (-6 : ℤ), (14 : ℤ)),
    ((-1 : ℤ), (0 : ℤ), (0 : ℤ))
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This expands the 187 generated structures and checks their coefficient keys.
theorem degreeFiveStageFourTopTriples_checked :
    degreeFiveStageFourEntries.map (fun entry =>
      (entry.a4, entry.a3, entry.a2)) =
        degreeFiveStageFourTopTriples := by
  simp only [degreeFiveStageFourEntries, List.map_append,
    degreeFiveStageFourEntriesChunk000, degreeFiveStageFourEntriesChunk001, degreeFiveStageFourEntriesChunk002, degreeFiveStageFourEntriesChunk003, degreeFiveStageFourEntriesChunk004, degreeFiveStageFourEntriesChunk005, degreeFiveStageFourEntriesChunk006, degreeFiveStageFourEntriesChunk007,
    degreeFiveStageFourTopTriples]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact 191 = 187 + 4 partition.
theorem degreeFiveStageFour_partition :
    degreeFiveStageThreePrefixes.toFinset =
      degreeFiveStageFourTopTriples.toFinset ∪
        degreeFiveStageFourRejectedTriples.toFinset := by
  decide

theorem degreeFiveStageFourEntries_valid :
    degreeFiveStageFourEntries.Forall
      DegreeFiveStageFourEntry.Valid := by
  simp only [degreeFiveStageFourEntries, List.forall_append]
  exact ⟨⟨⟨⟨⟨⟨⟨degreeFiveStageFourEntriesChunk000_valid, degreeFiveStageFourEntriesChunk001_valid⟩, degreeFiveStageFourEntriesChunk002_valid⟩, degreeFiveStageFourEntriesChunk003_valid⟩, degreeFiveStageFourEntriesChunk004_valid⟩, degreeFiveStageFourEntriesChunk005_valid⟩, degreeFiveStageFourEntriesChunk006_valid⟩, degreeFiveStageFourEntriesChunk007_valid⟩

theorem degreeFiveStageFourRanges_checked :
    degreeFiveStageFourEntries.map (fun entry =>
      (entry.a4, entry.a3, entry.a2,
        quarticTranslationLowerBound entry.baseCoefficients
          (-10) 10 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot)) =
      degreeFiveStageFourExpectedRanges := by
  simp only [degreeFiveStageFourEntries,
    degreeFiveStageFourExpectedRanges, List.map_append,
    degreeFiveStageFourRangesChunk000_checked, degreeFiveStageFourRangesChunk001_checked, degreeFiveStageFourRangesChunk002_checked, degreeFiveStageFourRangesChunk003_checked, degreeFiveStageFourRangesChunk004_checked, degreeFiveStageFourRangesChunk005_checked, degreeFiveStageFourRangesChunk006_checked, degreeFiveStageFourRangesChunk007_checked]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Computing the total length unfolds all 187 generated entries.
theorem degreeFiveStageFour_entry_count :
    degreeFiveStageFourEntries.length = 187 := by
  norm_num [degreeFiveStageFourEntries,
    degreeFiveStageFourEntriesChunk000, degreeFiveStageFourEntriesChunk001, degreeFiveStageFourEntriesChunk002, degreeFiveStageFourEntriesChunk003, degreeFiveStageFourEntriesChunk004, degreeFiveStageFourEntriesChunk005, degreeFiveStageFourEntriesChunk006, degreeFiveStageFourEntriesChunk007]

theorem degreeFiveStageFour_prefix_count :
    (degreeFiveStageFourEntries.flatMap fun entry =>
      entry.a1Candidates.toList.map fun a1 =>
        (entry.a4, entry.a3, entry.a2, a1)).length = 900 := by
  simp only [degreeFiveStageFourEntries, List.flatMap_append,
    List.length_append, degreeFiveStageFourPrefixCountChunk000, degreeFiveStageFourPrefixCountChunk001, degreeFiveStageFourPrefixCountChunk002, degreeFiveStageFourPrefixCountChunk003, degreeFiveStageFourPrefixCountChunk004, degreeFiveStageFourPrefixCountChunk005, degreeFiveStageFourPrefixCountChunk006, degreeFiveStageFourPrefixCountChunk007]

end TraceEuclidean
