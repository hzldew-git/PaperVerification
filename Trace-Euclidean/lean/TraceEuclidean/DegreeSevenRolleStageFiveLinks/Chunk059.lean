import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk059
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk046
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk047

/-! Generated local link between coverage and compact entry data, Chunk059. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk059 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk046.drop 303).take 697 ++
    (degreeSevenStageFiveEntriesChunk047.drop 0).take 8

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk059_valid :
    degreeSevenStageFiveAlignedEntriesChunk059.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk046.drop 303).take 697).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk046_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk047.drop 0).take 8).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk047_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk059,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk059_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk059.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk059.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk059_length :
    degreeSevenStageFiveAlignedEntriesChunk059.length = 705 := by
  rfl

end TraceEuclidean
