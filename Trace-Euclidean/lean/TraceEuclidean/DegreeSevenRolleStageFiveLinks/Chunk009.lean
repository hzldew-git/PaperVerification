import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk009
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk008
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk009

/-! Generated local link between coverage and compact entry data, Chunk009. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk009 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk008.drop 473).take 527 ++
    (degreeSevenStageFiveEntriesChunk009.drop 0).take 197

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk009_valid :
    degreeSevenStageFiveAlignedEntriesChunk009.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk008.drop 473).take 527).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk008_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk009.drop 0).take 197).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk009_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk009,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk009_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk009.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk009.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk009_length :
    degreeSevenStageFiveAlignedEntriesChunk009.length = 724 := by
  rfl

end TraceEuclidean
