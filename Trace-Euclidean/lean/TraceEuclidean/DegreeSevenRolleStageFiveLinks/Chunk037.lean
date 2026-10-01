import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk037
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk029
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk030

/-! Generated local link between coverage and compact entry data, Chunk037. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk037 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk029.drop 342).take 658 ++
    (degreeSevenStageFiveEntriesChunk030.drop 0).take 990

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk037_valid :
    degreeSevenStageFiveAlignedEntriesChunk037.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk029.drop 342).take 658).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk029_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk030.drop 0).take 990).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk030_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk037,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk037_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk037.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk037.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk037_length :
    degreeSevenStageFiveAlignedEntriesChunk037.length = 1648 := by
  rfl

end TraceEuclidean
