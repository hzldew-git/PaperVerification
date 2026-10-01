import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk021
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk017
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk018

/-! Generated local link between coverage and compact entry data, Chunk021. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk021 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk017.drop 558).take 442 ++
    (degreeSevenStageFiveEntriesChunk018.drop 0).take 738

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk021_valid :
    degreeSevenStageFiveAlignedEntriesChunk021.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk017.drop 558).take 442).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk017_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk018.drop 0).take 738).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk018_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk021,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk021_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk021.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk021.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk021_length :
    degreeSevenStageFiveAlignedEntriesChunk021.length = 1180 := by
  rfl

end TraceEuclidean
