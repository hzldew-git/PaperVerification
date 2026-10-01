import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk024
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk020
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk021

/-! Generated local link between coverage and compact entry data, Chunk024. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk024 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk020.drop 294).take 706 ++
    (degreeSevenStageFiveEntriesChunk021.drop 0).take 452

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk024_valid :
    degreeSevenStageFiveAlignedEntriesChunk024.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk020.drop 294).take 706).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk020_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk021.drop 0).take 452).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk021_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk024,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk024_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk024.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk024.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk024_length :
    degreeSevenStageFiveAlignedEntriesChunk024.length = 1158 := by
  rfl

end TraceEuclidean
