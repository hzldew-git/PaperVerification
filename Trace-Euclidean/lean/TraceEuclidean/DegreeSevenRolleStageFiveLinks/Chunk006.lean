import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk006
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk006
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk007

/-! Generated local link between coverage and compact entry data, Chunk006. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk006 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk006.drop 134).take 866 ++
    (degreeSevenStageFiveEntriesChunk007.drop 0).take 224

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk006_valid :
    degreeSevenStageFiveAlignedEntriesChunk006.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk006.drop 134).take 866).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk006_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk007.drop 0).take 224).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk007_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk006,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk006_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk006.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk006.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk006_length :
    degreeSevenStageFiveAlignedEntriesChunk006.length = 1090 := by
  rfl

end TraceEuclidean
