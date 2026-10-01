import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk040
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk032
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk033

/-! Generated local link between coverage and compact entry data, Chunk040. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk040 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk032.drop 868).take 132 ++
    (degreeSevenStageFiveEntriesChunk033.drop 0).take 187

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk040_valid :
    degreeSevenStageFiveAlignedEntriesChunk040.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk032.drop 868).take 132).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk032_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk033.drop 0).take 187).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk033_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk040,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk040_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk040.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk040.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk040_length :
    degreeSevenStageFiveAlignedEntriesChunk040.length = 319 := by
  rfl

end TraceEuclidean
