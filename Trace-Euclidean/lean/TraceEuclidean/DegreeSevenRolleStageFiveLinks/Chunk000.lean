import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk000
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk000

/-! Generated local link between coverage and compact entry data, Chunk000. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk000 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk000.drop 0).take 765

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk000_valid :
    degreeSevenStageFiveAlignedEntriesChunk000.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk000.drop 0).take 765).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk000_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk000,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk000_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk000.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk000.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk000_length :
    degreeSevenStageFiveAlignedEntriesChunk000.length = 765 := by
  rfl

end TraceEuclidean
