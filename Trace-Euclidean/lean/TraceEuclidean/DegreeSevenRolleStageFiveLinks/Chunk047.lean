import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk047
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk036
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk037

/-! Generated local link between coverage and compact entry data, Chunk047. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk047 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk036.drop 899).take 101 ++
    (degreeSevenStageFiveEntriesChunk037.drop 0).take 185

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk047_valid :
    degreeSevenStageFiveAlignedEntriesChunk047.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk036.drop 899).take 101).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk036_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk037.drop 0).take 185).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk037_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk047,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk047_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk047.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk047.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk047_length :
    degreeSevenStageFiveAlignedEntriesChunk047.length = 286 := by
  rfl

end TraceEuclidean
