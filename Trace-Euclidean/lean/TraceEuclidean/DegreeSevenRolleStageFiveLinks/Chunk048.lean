import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk048
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk037

/-! Generated local link between coverage and compact entry data, Chunk048. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk048 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk037.drop 185).take 219

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk048_valid :
    degreeSevenStageFiveAlignedEntriesChunk048.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk037.drop 185).take 219).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk037_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk048,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk048_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk048.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk048.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk048_length :
    degreeSevenStageFiveAlignedEntriesChunk048.length = 219 := by
  rfl

end TraceEuclidean
