import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk053
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk040
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk041
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk042

/-! Generated local link between coverage and compact entry data, Chunk053. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk053 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk040.drop 801).take 199 ++
    degreeSevenStageFiveEntriesChunk041 ++
    (degreeSevenStageFiveEntriesChunk042.drop 0).take 435

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk053_valid :
    degreeSevenStageFiveAlignedEntriesChunk053.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk040.drop 801).take 199).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk040_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk042.drop 0).take 435).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk042_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk053,
    List.forall_append]
  exact ⟨⟨hpiece0, degreeSevenStageFiveEntriesChunk041_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk053_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk053.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk053.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk053_length :
    degreeSevenStageFiveAlignedEntriesChunk053.length = 1634 := by
  rfl

end TraceEuclidean
