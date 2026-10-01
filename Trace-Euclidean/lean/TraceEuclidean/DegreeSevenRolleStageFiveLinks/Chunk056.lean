import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk056
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk043
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk044

/-! Generated local link between coverage and compact entry data, Chunk056. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk056 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk043.drop 961).take 39 ++
    (degreeSevenStageFiveEntriesChunk044.drop 0).take 991

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk056_valid :
    degreeSevenStageFiveAlignedEntriesChunk056.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk043.drop 961).take 39).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk043_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk044.drop 0).take 991).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk044_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk056,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk056_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk056.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk056.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk056_length :
    degreeSevenStageFiveAlignedEntriesChunk056.length = 1030 := by
  rfl

end TraceEuclidean
