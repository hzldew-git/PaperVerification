import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk064
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk048

/-! Generated local link between coverage and compact entry data, Chunk064. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk064 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk048.drop 414).take 159

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk064_valid :
    degreeSevenStageFiveAlignedEntriesChunk064.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk048.drop 414).take 159).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk048_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk064,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk064_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk064.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk064.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk064_length :
    degreeSevenStageFiveAlignedEntriesChunk064.length = 159 := by
  rfl

end TraceEuclidean
