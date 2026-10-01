import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk027
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk022
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk023

/-! Generated local link between coverage and compact entry data, Chunk027. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk027 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk022.drop 644).take 356 ++
    (degreeSevenStageFiveEntriesChunk023.drop 0).take 322

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk027_valid :
    degreeSevenStageFiveAlignedEntriesChunk027.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk022.drop 644).take 356).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk022_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk023.drop 0).take 322).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk023_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk027,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk027_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk027.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk027.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk027_length :
    degreeSevenStageFiveAlignedEntriesChunk027.length = 678 := by
  rfl

end TraceEuclidean
