import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk062
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk047
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk048

/-! Generated local link between coverage and compact entry data, Chunk062. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk062 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk047.drop 809).take 191 ++
    (degreeSevenStageFiveEntriesChunk048.drop 0).take 180

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk062_valid :
    degreeSevenStageFiveAlignedEntriesChunk062.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk047.drop 809).take 191).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk047_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk048.drop 0).take 180).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk048_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk062,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk062_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk062.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk062.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk062_length :
    degreeSevenStageFiveAlignedEntriesChunk062.length = 371 := by
  rfl

end TraceEuclidean
