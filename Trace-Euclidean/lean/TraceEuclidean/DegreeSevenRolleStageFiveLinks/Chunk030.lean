import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk030
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk024

/-! Generated local link between coverage and compact entry data, Chunk030. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk030 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk024.drop 15).take 320

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk030_valid :
    degreeSevenStageFiveAlignedEntriesChunk030.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk024.drop 15).take 320).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk024_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk030,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk030_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk030.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk030.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk030_length :
    degreeSevenStageFiveAlignedEntriesChunk030.length = 320 := by
  rfl

end TraceEuclidean
