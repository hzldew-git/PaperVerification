import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk002
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk002
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk003

/-! Generated local link between coverage and compact entry data, Chunk002. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk002 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk002.drop 859).take 141 ++
    (degreeSevenStageFiveEntriesChunk003.drop 0).take 176

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk002_valid :
    degreeSevenStageFiveAlignedEntriesChunk002.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk002.drop 859).take 141).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk002_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk003.drop 0).take 176).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk003_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk002,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk002_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk002.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk002.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk002_length :
    degreeSevenStageFiveAlignedEntriesChunk002.length = 317 := by
  rfl

end TraceEuclidean
