import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk035
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk027
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk028

/-! Generated local link between coverage and compact entry data, Chunk035. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk035 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk027.drop 818).take 182 ++
    (degreeSevenStageFiveEntriesChunk028.drop 0).take 287

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk035_valid :
    degreeSevenStageFiveAlignedEntriesChunk035.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk027.drop 818).take 182).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk027_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk028.drop 0).take 287).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk028_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk035,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk035_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk035.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk035.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk035_length :
    degreeSevenStageFiveAlignedEntriesChunk035.length = 469 := by
  rfl

end TraceEuclidean
