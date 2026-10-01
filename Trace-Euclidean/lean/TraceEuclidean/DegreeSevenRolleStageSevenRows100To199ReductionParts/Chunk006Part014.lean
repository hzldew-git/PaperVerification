import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 14 for Stage Five rows 160 through 169. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (5 : ℤ), (17 : ℤ), (9 : ℤ), (1 : ℤ), (16777216 : ℤ), (-23929899 : ℤ), (-23929896 : ℤ), (-10705129 : ℤ), (-10705126 : ℤ), (-7778490 : ℤ), (-7778487 : ℤ), (-1147635 : ℤ), (-1147632 : ℤ), (21301144 : ℤ), (21301147 : ℤ), (65401413 : ℤ), (65401416 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (5 : ℤ), (17 : ℤ), (10 : ℤ), (2 : ℤ), (16777216 : ℤ), (-24217468 : ℤ), (-24217465 : ℤ), (-9780134 : ℤ), (-9780131 : ℤ), (-7135971 : ℤ), (-7135968 : ℤ), (-2673556 : ℤ), (-2673553 : ℤ), (21566335 : ℤ), (21566338 : ℤ), (65382197 : ℤ), (65382200 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014.length =
      2 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014).length =
      0 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk006Part014).length =
      0 := by
  rfl

end

end TraceEuclidean
