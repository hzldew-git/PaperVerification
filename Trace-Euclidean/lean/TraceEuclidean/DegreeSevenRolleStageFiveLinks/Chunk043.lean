import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk043
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk034
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk035

/-! Generated local link between coverage and compact entry data, Chunk043. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk043 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk034.drop 717).take 283 ++
    (degreeSevenStageFiveEntriesChunk035.drop 0).take 670

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk043_valid :
    degreeSevenStageFiveAlignedEntriesChunk043.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk034.drop 717).take 283).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk034_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece1 :
      ((degreeSevenStageFiveEntriesChunk035.drop 0).take 670).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk035_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk043,
    List.forall_append]
  exact ⟨hpiece0, hpiece1⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk043_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk043.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk043.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk043_length :
    degreeSevenStageFiveAlignedEntriesChunk043.length = 953 := by
  rfl

end TraceEuclidean
