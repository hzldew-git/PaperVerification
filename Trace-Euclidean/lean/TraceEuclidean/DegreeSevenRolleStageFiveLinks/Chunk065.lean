import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk065
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk048

/-! Generated local link between coverage and compact entry data, Chunk065. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk065 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk048.drop 573).take 21

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk065_valid :
    degreeSevenStageFiveAlignedEntriesChunk065.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk048.drop 573).take 21).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk048_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk065,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk065_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk065.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk065.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk065_length :
    degreeSevenStageFiveAlignedEntriesChunk065.length = 21 := by
  rfl

end TraceEuclidean
