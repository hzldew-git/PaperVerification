import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk060
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk047

/-! Generated local link between coverage and compact entry data, Chunk060. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk060 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk047.drop 8).take 304

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk060_valid :
    degreeSevenStageFiveAlignedEntriesChunk060.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk047.drop 8).take 304).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk047_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk060,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk060_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk060.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk060.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk060_length :
    degreeSevenStageFiveAlignedEntriesChunk060.length = 304 := by
  rfl

end TraceEuclidean
