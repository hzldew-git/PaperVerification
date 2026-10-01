import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk042
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk034

/-! Generated local link between coverage and compact entry data, Chunk042. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk042 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk034.drop 385).take 332

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk042_valid :
    degreeSevenStageFiveAlignedEntriesChunk042.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk034.drop 385).take 332).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk034_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk042,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk042_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk042.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk042.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk042_length :
    degreeSevenStageFiveAlignedEntriesChunk042.length = 332 := by
  rfl

end TraceEuclidean
