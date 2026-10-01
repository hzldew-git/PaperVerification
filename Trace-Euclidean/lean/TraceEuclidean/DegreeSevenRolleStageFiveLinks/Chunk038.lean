import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk038
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk030
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk031

/-! Generated local link between coverage and compact entry data, Chunk038. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk038 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk030.drop 990).take 10 ++
    (degreeSevenStageFiveEntriesChunk031.drop 0).take 266

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk038_valid :
    degreeSevenStageFiveAlignedEntriesChunk038.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk030.drop 990).take 10).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk030_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk031.drop 0).take 266).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk031_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk038,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk038_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk038.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk038.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk038_length :
    degreeSevenStageFiveAlignedEntriesChunk038.length = 276 := by
  rfl

end TraceEuclidean
