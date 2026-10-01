import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk054
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk042
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk043

/-! Generated local link between coverage and compact entry data, Chunk054. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk054 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk042.drop 435).take 565 ++
    (degreeSevenStageFiveEntriesChunk043.drop 0).take 178

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk054_valid :
    degreeSevenStageFiveAlignedEntriesChunk054.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk042.drop 435).take 565).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk042_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk043.drop 0).take 178).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk043_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk054,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk054_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk054.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk054.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk054_length :
    degreeSevenStageFiveAlignedEntriesChunk054.length = 743 := by
  rfl

end TraceEuclidean
