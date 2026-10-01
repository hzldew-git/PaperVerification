import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk057
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk044
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk045

/-! Generated local link between coverage and compact entry data, Chunk057. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk057 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk044.drop 991).take 9 ++
    (degreeSevenStageFiveEntriesChunk045.drop 0).take 546

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk057_valid :
    degreeSevenStageFiveAlignedEntriesChunk057.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk044.drop 991).take 9).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk044_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk045.drop 0).take 546).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk045_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk057,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk057_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk057.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk057.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk057_length :
    degreeSevenStageFiveAlignedEntriesChunk057.length = 555 := by
  rfl

end TraceEuclidean
