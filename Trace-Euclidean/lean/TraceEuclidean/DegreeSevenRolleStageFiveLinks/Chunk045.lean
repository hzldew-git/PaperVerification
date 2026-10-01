import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk045
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk036

/-! Generated local link between coverage and compact entry data, Chunk045. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk045 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk036.drop 57).take 413

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk045_valid :
    degreeSevenStageFiveAlignedEntriesChunk045.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk036.drop 57).take 413).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk036_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk045,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk045_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk045.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk045.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk045_length :
    degreeSevenStageFiveAlignedEntriesChunk045.length = 413 := by
  rfl

end TraceEuclidean
