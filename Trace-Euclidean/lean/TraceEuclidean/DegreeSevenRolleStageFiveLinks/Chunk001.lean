import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk001
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk000
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk001
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk002

/-! Generated local link between coverage and compact entry data, Chunk001. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk001 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk000.drop 765).take 235 ++
    degreeSevenStageFiveEntriesChunk001 ++
    (degreeSevenStageFiveEntriesChunk002.drop 0).take 859

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk001_valid :
    degreeSevenStageFiveAlignedEntriesChunk001.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk000.drop 765).take 235).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk000_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk002.drop 0).take 859).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk002_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk001,
    List.forall_append]
  exact ⟨⟨hpiece0, degreeSevenStageFiveEntriesChunk001_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk001_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk001.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk001.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk001_length :
    degreeSevenStageFiveAlignedEntriesChunk001.length = 2094 := by
  rfl

end TraceEuclidean
