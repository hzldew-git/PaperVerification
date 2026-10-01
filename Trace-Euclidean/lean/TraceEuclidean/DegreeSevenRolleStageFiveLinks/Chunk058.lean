import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk058
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk045
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk046

/-! Generated local link between coverage and compact entry data, Chunk058. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk058 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk045.drop 546).take 454 ++
    (degreeSevenStageFiveEntriesChunk046.drop 0).take 303

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk058_valid :
    degreeSevenStageFiveAlignedEntriesChunk058.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk045.drop 546).take 454).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk045_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk046.drop 0).take 303).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk046_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk058,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk058_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk058.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk058.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk058_length :
    degreeSevenStageFiveAlignedEntriesChunk058.length = 757 := by
  rfl

end TraceEuclidean
