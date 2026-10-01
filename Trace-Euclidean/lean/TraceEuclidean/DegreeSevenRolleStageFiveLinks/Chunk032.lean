import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk032
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk024

/-! Generated local link between coverage and compact entry data, Chunk032. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk032 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk024.drop 571).take 60

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk032_valid :
    degreeSevenStageFiveAlignedEntriesChunk032.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk024.drop 571).take 60).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk024_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk032,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk032_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk032.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk032.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk032_length :
    degreeSevenStageFiveAlignedEntriesChunk032.length = 60 := by
  rfl

end TraceEuclidean
