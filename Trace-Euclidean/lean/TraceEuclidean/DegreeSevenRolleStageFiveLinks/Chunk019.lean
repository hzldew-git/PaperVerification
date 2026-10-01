import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk019
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk015
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk016
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk017

/-! Generated local link between coverage and compact entry data, Chunk019. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk019 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk015.drop 21).take 979 ++
    degreeSevenStageFiveEntriesChunk016 ++
    (degreeSevenStageFiveEntriesChunk017.drop 0).take 128

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk019_valid :
    degreeSevenStageFiveAlignedEntriesChunk019.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk015.drop 21).take 979).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk015_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk017.drop 0).take 128).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk017_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk019,
    List.forall_append]
  exact ⟨⟨hpiece0, degreeSevenStageFiveEntriesChunk016_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk019_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk019.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk019.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk019_length :
    degreeSevenStageFiveAlignedEntriesChunk019.length = 2107 := by
  rfl

end TraceEuclidean
