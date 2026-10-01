import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk029
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk023
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk024

/-! Generated local link between coverage and compact entry data, Chunk029. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk029 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk023.drop 611).take 389 ++
    (degreeSevenStageFiveEntriesChunk024.drop 0).take 15

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk029_valid :
    degreeSevenStageFiveAlignedEntriesChunk029.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk023.drop 611).take 389).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk023_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk024.drop 0).take 15).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk024_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk029,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk029_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk029.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk029.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk029_length :
    degreeSevenStageFiveAlignedEntriesChunk029.length = 404 := by
  rfl

end TraceEuclidean
