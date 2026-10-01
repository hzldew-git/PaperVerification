import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk031
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk024

/-! Generated local link between coverage and compact entry data, Chunk031. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk031 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk024.drop 335).take 236

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk031_valid :
    degreeSevenStageFiveAlignedEntriesChunk031.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk024.drop 335).take 236).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk024_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk031,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk031_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk031.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk031.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk031_length :
    degreeSevenStageFiveAlignedEntriesChunk031.length = 236 := by
  rfl

end TraceEuclidean
