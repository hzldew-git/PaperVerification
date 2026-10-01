import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk028
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk023

/-! Generated local link between coverage and compact entry data, Chunk028. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk028 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk023.drop 322).take 289

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk028_valid :
    degreeSevenStageFiveAlignedEntriesChunk028.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk023.drop 322).take 289).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk023_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk028,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk028_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk028.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk028.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk028_length :
    degreeSevenStageFiveAlignedEntriesChunk028.length = 289 := by
  rfl

end TraceEuclidean
