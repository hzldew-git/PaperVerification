import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk055
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk043

/-! Generated local link between coverage and compact entry data, Chunk055. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk055 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk043.drop 178).take 783

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk055_valid :
    degreeSevenStageFiveAlignedEntriesChunk055.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk043.drop 178).take 783).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk043_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk055,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk055_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk055.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk055.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk055_length :
    degreeSevenStageFiveAlignedEntriesChunk055.length = 783 := by
  rfl

end TraceEuclidean
