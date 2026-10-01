import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk020
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk017

/-! Generated local link between coverage and compact entry data, Chunk020. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk020 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk017.drop 128).take 430

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk020_valid :
    degreeSevenStageFiveAlignedEntriesChunk020.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk017.drop 128).take 430).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk017_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk020,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk020_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk020.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk020.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk020_length :
    degreeSevenStageFiveAlignedEntriesChunk020.length = 430 := by
  rfl

end TraceEuclidean
