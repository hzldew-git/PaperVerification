import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk011
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk009

/-! Generated local link between coverage and compact entry data, Chunk011. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk011 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk009.drop 501).take 401

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk011_valid :
    degreeSevenStageFiveAlignedEntriesChunk011.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk009.drop 501).take 401).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk009_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk011,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk011_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk011.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk011.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk011_length :
    degreeSevenStageFiveAlignedEntriesChunk011.length = 401 := by
  rfl

end TraceEuclidean
