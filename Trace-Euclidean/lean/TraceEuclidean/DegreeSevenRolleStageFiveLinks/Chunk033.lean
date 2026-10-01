import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk033
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk024
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk025

/-! Generated local link between coverage and compact entry data, Chunk033. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk033 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk024.drop 631).take 369 ++
    (degreeSevenStageFiveEntriesChunk025.drop 0).take 434

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk033_valid :
    degreeSevenStageFiveAlignedEntriesChunk033.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk024.drop 631).take 369).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk024_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk025.drop 0).take 434).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk025_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk033,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk033_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk033.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk033.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk033_length :
    degreeSevenStageFiveAlignedEntriesChunk033.length = 803 := by
  rfl

end TraceEuclidean
