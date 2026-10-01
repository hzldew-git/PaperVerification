import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk010
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk009

/-! Generated local link between coverage and compact entry data, Chunk010. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk010 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk009.drop 197).take 304

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk010_valid :
    degreeSevenStageFiveAlignedEntriesChunk010.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk009.drop 197).take 304).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk009_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk010,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk010_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk010.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk010.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk010_length :
    degreeSevenStageFiveAlignedEntriesChunk010.length = 304 := by
  rfl

end TraceEuclidean
