import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk041
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk033
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk034

/-! Generated local link between coverage and compact entry data, Chunk041. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk041 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk033.drop 187).take 813 ++
    (degreeSevenStageFiveEntriesChunk034.drop 0).take 385

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk041_valid :
    degreeSevenStageFiveAlignedEntriesChunk041.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk033.drop 187).take 813).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk033_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk034.drop 0).take 385).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk034_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk041,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk041_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk041.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk041.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk041_length :
    degreeSevenStageFiveAlignedEntriesChunk041.length = 1198 := by
  rfl

end TraceEuclidean
