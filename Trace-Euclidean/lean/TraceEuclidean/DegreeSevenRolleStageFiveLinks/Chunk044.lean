import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk044
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk035
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk036

/-! Generated local link between coverage and compact entry data, Chunk044. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk044 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk035.drop 670).take 330 ++
    (degreeSevenStageFiveEntriesChunk036.drop 0).take 57

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk044_valid :
    degreeSevenStageFiveAlignedEntriesChunk044.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk035.drop 670).take 330).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk035_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk036.drop 0).take 57).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk036_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk044,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk044_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk044.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk044.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk044_length :
    degreeSevenStageFiveAlignedEntriesChunk044.length = 387 := by
  rfl

end TraceEuclidean
