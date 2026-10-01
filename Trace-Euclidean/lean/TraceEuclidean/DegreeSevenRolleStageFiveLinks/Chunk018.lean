import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk018
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk014
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk015

/-! Generated local link between coverage and compact entry data, Chunk018. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk018 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk014.drop 522).take 478 ++
    (degreeSevenStageFiveEntriesChunk015.drop 0).take 21

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk018_valid :
    degreeSevenStageFiveAlignedEntriesChunk018.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk014.drop 522).take 478).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk014_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk015.drop 0).take 21).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk015_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk018,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk018_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk018.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk018.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk018_length :
    degreeSevenStageFiveAlignedEntriesChunk018.length = 499 := by
  rfl

end TraceEuclidean
