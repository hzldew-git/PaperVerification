import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk039
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk031
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk032

/-! Generated local link between coverage and compact entry data, Chunk039. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk039 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk031.drop 266).take 734 ++
    (degreeSevenStageFiveEntriesChunk032.drop 0).take 868

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk039_valid :
    degreeSevenStageFiveAlignedEntriesChunk039.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk031.drop 266).take 734).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk031_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk032.drop 0).take 868).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk032_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk039,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk039_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk039.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk039.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk039_length :
    degreeSevenStageFiveAlignedEntriesChunk039.length = 1602 := by
  rfl

end TraceEuclidean
