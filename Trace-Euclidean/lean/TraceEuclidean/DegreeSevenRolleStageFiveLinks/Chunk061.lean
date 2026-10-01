import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk061
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk047

/-! Generated local link between coverage and compact entry data, Chunk061. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk061 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk047.drop 312).take 497

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk061_valid :
    degreeSevenStageFiveAlignedEntriesChunk061.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk047.drop 312).take 497).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk047_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk061,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk061_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk061.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk061.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk061_length :
    degreeSevenStageFiveAlignedEntriesChunk061.length = 497 := by
  rfl

end TraceEuclidean
