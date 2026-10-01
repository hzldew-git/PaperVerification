import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk046
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk036

/-! Generated local link between coverage and compact entry data, Chunk046. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk046 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk036.drop 470).take 429

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk046_valid :
    degreeSevenStageFiveAlignedEntriesChunk046.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk036.drop 470).take 429).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk036_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk046,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk046_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk046.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk046.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk046_length :
    degreeSevenStageFiveAlignedEntriesChunk046.length = 429 := by
  rfl

end TraceEuclidean
