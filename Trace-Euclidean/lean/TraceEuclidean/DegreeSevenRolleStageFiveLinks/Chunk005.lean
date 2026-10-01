import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk005
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk005
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk006

/-! Generated local link between coverage and compact entry data, Chunk005. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk005 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk005.drop 497).take 503 ++
    (degreeSevenStageFiveEntriesChunk006.drop 0).take 134

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk005_valid :
    degreeSevenStageFiveAlignedEntriesChunk005.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk005.drop 497).take 503).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk005_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk006.drop 0).take 134).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk006_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk005,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk005_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk005.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk005.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk005_length :
    degreeSevenStageFiveAlignedEntriesChunk005.length = 637 := by
  rfl

end TraceEuclidean
