import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk016
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk011
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk012
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk013

/-! Generated local link between coverage and compact entry data, Chunk016. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk016 :
    List DegreeSevenStageFiveDyadicEntry :=
  degreeSevenStageFiveEntriesChunk011 ++
    degreeSevenStageFiveEntriesChunk012 ++
    (degreeSevenStageFiveEntriesChunk013.drop 0).take 446

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk016_valid :
    degreeSevenStageFiveAlignedEntriesChunk016.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece2 :
      ((degreeSevenStageFiveEntriesChunk013.drop 0).take 446).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk013_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk016,
    List.forall_append]
  exact ⟨⟨degreeSevenStageFiveEntriesChunk011_valid, degreeSevenStageFiveEntriesChunk012_valid⟩, hpiece2⟩

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk016_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk016.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk016.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk016_length :
    degreeSevenStageFiveAlignedEntriesChunk016.length = 2446 := by
  rfl

end TraceEuclidean
