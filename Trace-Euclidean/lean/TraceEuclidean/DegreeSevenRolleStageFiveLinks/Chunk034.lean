import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk034
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk025
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk026
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk027

/-! Generated local link between coverage and compact entry data, Chunk034. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk034 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk025.drop 434).take 566 ++
    degreeSevenStageFiveEntriesChunk026 ++
    (degreeSevenStageFiveEntriesChunk027.drop 0).take 818

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk034_valid :
    degreeSevenStageFiveAlignedEntriesChunk034.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk025.drop 434).take 566).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk025_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk027.drop 0).take 818).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk027_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk034,
    List.forall_append]
  exact ⟨⟨hpiece0, degreeSevenStageFiveEntriesChunk026_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk034_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk034.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk034.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk034_length :
    degreeSevenStageFiveAlignedEntriesChunk034.length = 2384 := by
  rfl

end TraceEuclidean
