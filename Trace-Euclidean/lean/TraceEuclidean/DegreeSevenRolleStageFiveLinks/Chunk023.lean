import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk023
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk019
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk020

/-! Generated local link between coverage and compact entry data, Chunk023. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk023 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk019.drop 808).take 192 ++
    (degreeSevenStageFiveEntriesChunk020.drop 0).take 294

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk023_valid :
    degreeSevenStageFiveAlignedEntriesChunk023.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk019.drop 808).take 192).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk019_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk020.drop 0).take 294).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk020_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk023,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk023_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk023.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk023.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk023_length :
    degreeSevenStageFiveAlignedEntriesChunk023.length = 486 := by
  rfl

end TraceEuclidean
