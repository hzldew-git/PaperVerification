import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk007
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk007

/-! Generated local link between coverage and compact entry data, Chunk007. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk007 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk007.drop 224).take 507

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk007_valid :
    degreeSevenStageFiveAlignedEntriesChunk007.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk007.drop 224).take 507).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk007_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk007,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk007_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk007.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk007.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk007_length :
    degreeSevenStageFiveAlignedEntriesChunk007.length = 507 := by
  rfl

end TraceEuclidean
