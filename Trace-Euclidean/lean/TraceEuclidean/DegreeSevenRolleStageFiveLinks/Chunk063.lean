import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk063
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk048

/-! Generated local link between coverage and compact entry data, Chunk063. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk063 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk048.drop 180).take 234

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk063_valid :
    degreeSevenStageFiveAlignedEntriesChunk063.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk048.drop 180).take 234).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk048_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk063,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk063_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk063.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk063.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk063_length :
    degreeSevenStageFiveAlignedEntriesChunk063.length = 234 := by
  rfl

end TraceEuclidean
