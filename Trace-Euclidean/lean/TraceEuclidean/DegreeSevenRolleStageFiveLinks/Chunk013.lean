import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk013
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk010

/-! Generated local link between coverage and compact entry data, Chunk013. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk013 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk010.drop 243).take 249

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk013_valid :
    degreeSevenStageFiveAlignedEntriesChunk013.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk010.drop 243).take 249).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk010_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk013,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk013_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk013.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk013.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk013_length :
    degreeSevenStageFiveAlignedEntriesChunk013.length = 249 := by
  rfl

end TraceEuclidean
