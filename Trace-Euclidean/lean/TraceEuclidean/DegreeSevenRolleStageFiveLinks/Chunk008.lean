import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk008
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk007
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk008

/-! Generated local link between coverage and compact entry data, Chunk008. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk008 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk007.drop 731).take 269 ++
    (degreeSevenStageFiveEntriesChunk008.drop 0).take 473

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk008_valid :
    degreeSevenStageFiveAlignedEntriesChunk008.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk007.drop 731).take 269).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk007_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk008.drop 0).take 473).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk008_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk008,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk008_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk008.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk008.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk008_length :
    degreeSevenStageFiveAlignedEntriesChunk008.length = 742 := by
  rfl

end TraceEuclidean
