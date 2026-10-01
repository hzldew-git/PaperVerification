import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk026
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk021
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk022

/-! Generated local link between coverage and compact entry data, Chunk026. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk026 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk021.drop 957).take 43 ++
    (degreeSevenStageFiveEntriesChunk022.drop 0).take 644

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk026_valid :
    degreeSevenStageFiveAlignedEntriesChunk026.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk021.drop 957).take 43).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk021_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk022.drop 0).take 644).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk022_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk026,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk026_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk026.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk026.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk026_length :
    degreeSevenStageFiveAlignedEntriesChunk026.length = 687 := by
  rfl

end TraceEuclidean
