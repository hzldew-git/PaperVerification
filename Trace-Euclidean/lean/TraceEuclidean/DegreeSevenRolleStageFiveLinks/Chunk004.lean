import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk004
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk004
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk005

/-! Generated local link between coverage and compact entry data, Chunk004. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk004 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk004.drop 583).take 417 ++
    (degreeSevenStageFiveEntriesChunk005.drop 0).take 497

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk004_valid :
    degreeSevenStageFiveAlignedEntriesChunk004.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk004.drop 583).take 417).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk004_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk005.drop 0).take 497).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk005_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk004,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk004_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk004.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk004.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk004_length :
    degreeSevenStageFiveAlignedEntriesChunk004.length = 914 := by
  rfl

end TraceEuclidean
