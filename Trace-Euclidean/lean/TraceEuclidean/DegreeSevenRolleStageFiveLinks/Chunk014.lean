import TraceEuclidean.DegreeSevenRolleStageFiveCoverages.Chunk014
import TraceEuclidean.DegreeSevenRolleStageFiveCertificates.Chunk010

/-! Generated local link between coverage and compact entry data, Chunk014. -/

namespace TraceEuclidean

def degreeSevenStageFiveAlignedEntriesChunk014 :
    List DegreeSevenStageFiveDyadicEntry :=
  (degreeSevenStageFiveEntriesChunk010.drop 492).take 102

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk014_valid :
    degreeSevenStageFiveAlignedEntriesChunk014.Forall
      DegreeSevenStageFiveDyadicEntry.Valid := by
  have hpiece0 :
      ((degreeSevenStageFiveEntriesChunk010.drop 492).take 102).Forall
        DegreeSevenStageFiveDyadicEntry.Valid := by
    rw [List.forall_iff_forall_mem]
    intro entry hentry
    exact (List.forall_iff_forall_mem.mp degreeSevenStageFiveEntriesChunk010_valid)
      entry (List.mem_of_mem_drop
        (List.mem_of_mem_take hentry))
  simp only [degreeSevenStageFiveAlignedEntriesChunk014,
    List.forall_append]
  exact hpiece0

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk014_top_checked :
    degreeSevenStageFiveAlignedEntriesChunk014.map (fun entry =>
        (entry.a6, entry.a5, entry.a4, entry.a3)) =
      degreeSevenStageFiveCoveragesChunk014.flatMap
        DegreeSevenStageFiveCoverage.topQuadruples := by
  rfl

set_option maxRecDepth 100000 in
theorem degreeSevenStageFiveAlignedEntriesChunk014_length :
    degreeSevenStageFiveAlignedEntriesChunk014.length = 102 := by
  rfl

end TraceEuclidean
