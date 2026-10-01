import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk012
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk009
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk010

/-! Generated local link between coverage and compact entry data, Chunk012. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk012 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk009.drop 902).take 98 ++
    (degreeSevenStageFiveEntriesChunk010.drop 0).take 243

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk012_valid :
    degreeSevenStageFiveAlignedEntriesChunk012.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk009.drop 902).take 98).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk009_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk010.drop 0).take 243).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk010_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk012,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk012_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk012.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk012.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk012_length :
    degreeSevenStageFiveAlignedEntriesChunk012.length = 341 := by
  rfl

end TraceEuclidean
