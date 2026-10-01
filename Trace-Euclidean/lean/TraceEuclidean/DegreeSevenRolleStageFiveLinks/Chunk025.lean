import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk025
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk021

/-! Generated local link between coverage and compact entry data, Chunk025. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk025 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk021.drop 452).take 505

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk025_valid :
    degreeSevenStageFiveAlignedEntriesChunk025.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk021.drop 452).take 505).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk021_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk025,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk025_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk025.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk025.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk025_length :
    degreeSevenStageFiveAlignedEntriesChunk025.length = 505 := by
  rfl

end TraceEuclidean
