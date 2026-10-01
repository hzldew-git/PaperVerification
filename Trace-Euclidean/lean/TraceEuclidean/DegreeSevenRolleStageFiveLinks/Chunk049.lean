import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk049
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk037

/-! Generated local link between coverage and compact entry data, Chunk049. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk049 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk037.drop 404).take 53

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk049_valid :
    degreeSevenStageFiveAlignedEntriesChunk049.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk037.drop 404).take 53).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk037_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk049,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk049_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk049.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk049.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk049_length :
    degreeSevenStageFiveAlignedEntriesChunk049.length = 53 := by
  rfl

end TraceEuclidean
