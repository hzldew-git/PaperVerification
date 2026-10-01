import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk003
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk003
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk004

/-! Generated local link between coverage and compact entry data, Chunk003. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk003 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk003.drop 176).take 824 ++
    (degreeSevenStageFiveEntriesChunk004.drop 0).take 583

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk003_valid :
    degreeSevenStageFiveAlignedEntriesChunk003.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk003.drop 176).take 824).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk003_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk004.drop 0).take 583).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk004_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk003,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk003_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk003.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk003.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk003_length :
    degreeSevenStageFiveAlignedEntriesChunk003.length = 1407 := by
  rfl

end TraceEuclidean
