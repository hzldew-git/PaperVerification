import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk052
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk040

/-! Generated local link between coverage and compact entry data, Chunk052. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk052 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk040.drop 548).take 253

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk052_valid :
    degreeSevenStageFiveAlignedEntriesChunk052.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk040.drop 548).take 253).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk040_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk052,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk052_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk052.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk052.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk052_length :
    degreeSevenStageFiveAlignedEntriesChunk052.length = 253 := by
  rfl

end TraceEuclidean
