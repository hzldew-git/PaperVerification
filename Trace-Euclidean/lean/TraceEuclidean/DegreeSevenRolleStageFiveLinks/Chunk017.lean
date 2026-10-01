import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk017
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk013
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk014

/-! Generated local link between coverage and compact entry data, Chunk017. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk017 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk013.drop 446).take 554 ++
    (degreeSevenStageFiveEntriesChunk014.drop 0).take 522

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk017_valid :
    degreeSevenStageFiveAlignedEntriesChunk017.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk013.drop 446).take 554).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk013_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk014.drop 0).take 522).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk014_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk017,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk017_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk017.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk017.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk017_length :
    degreeSevenStageFiveAlignedEntriesChunk017.length = 1076 := by
  rfl

end TraceEuclidean
