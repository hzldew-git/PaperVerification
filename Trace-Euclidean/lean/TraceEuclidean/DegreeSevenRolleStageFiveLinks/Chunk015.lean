import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk015
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk010

/-! Generated local link between coverage and compact entry data, Chunk015. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk015 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk010.drop 594).take 406

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk015_valid :
    degreeSevenStageFiveAlignedEntriesChunk015.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk010.drop 594).take 406).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk010_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk015,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk015_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk015.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk015.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk015_length :
    degreeSevenStageFiveAlignedEntriesChunk015.length = 406 := by
  rfl

end TraceEuclidean
