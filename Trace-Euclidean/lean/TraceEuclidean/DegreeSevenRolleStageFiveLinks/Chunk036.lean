import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk036
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk028
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk029

/-! Generated local link between coverage and compact entry data, Chunk036. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk036 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk028.drop 287).take 713 ++
    (degreeSevenStageFiveEntriesChunk029.drop 0).take 342

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk036_valid :
    degreeSevenStageFiveAlignedEntriesChunk036.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk028.drop 287).take 713).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk028_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk029.drop 0).take 342).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk029_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk036,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk036_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk036.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk036.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk036_length :
    degreeSevenStageFiveAlignedEntriesChunk036.length = 1055 := by
  rfl

end TraceEuclidean
