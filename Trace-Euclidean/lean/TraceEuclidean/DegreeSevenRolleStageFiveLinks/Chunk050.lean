import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk050
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk037
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk038

/-! Generated local link between coverage and compact entry data, Chunk050. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk050 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk037.drop 457).take 543 ++
    (degreeSevenStageFiveEntriesChunk038.drop 0).take 587

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk050_valid :
    degreeSevenStageFiveAlignedEntriesChunk050.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk037.drop 457).take 543).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk037_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk038.drop 0).take 587).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk038_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk050,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk050_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk050.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk050.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk050_length :
    degreeSevenStageFiveAlignedEntriesChunk050.length = 1130 := by
  rfl

end TraceEuclidean
