import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk051
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk038
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk039
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk040

/-! Generated local link between coverage and compact entry data, Chunk051. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk051 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk038.drop 587).take 413 ++
    degreeSevenStageFiveEntriesChunk039 ++
    (degreeSevenStageFiveEntriesChunk040.drop 0).take 548

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk051_valid :
    degreeSevenStageFiveAlignedEntriesChunk051.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk038.drop 587).take 413).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk038_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk040.drop 0).take 548).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk040_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk051,
    List.forall_append]
  exact ⟨⟨hpiece0, degreeSevenStageFiveEntriesChunk039_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk051_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk051.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk051.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk051_length :
    degreeSevenStageFiveAlignedEntriesChunk051.length = 1961 := by
  rfl

end TraceEuclidean
