import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk022
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk018
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk019

/-! Generated local link between coverage and compact entry data, Chunk022. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk022 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk018.drop 738).take 262 ++
    (degreeSevenStageFiveEntriesChunk019.drop 0).take 808

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk022_valid :
    degreeSevenStageFiveAlignedEntriesChunk022.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk018.drop 738).take 262).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk018_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk019.drop 0).take 808).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk019_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk022,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk022_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk022.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk022.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk022_length :
    degreeSevenStageFiveAlignedEntriesChunk022.length = 1070 := by
  rfl

end TraceEuclidean
