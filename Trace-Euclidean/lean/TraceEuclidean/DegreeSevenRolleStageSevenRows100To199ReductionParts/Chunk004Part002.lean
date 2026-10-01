import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 2 for Stage Five rows 140 through 149. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (24 : ℤ), (22 : ℤ), (8 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-13242722 : ℤ), (-13242719 : ℤ), (-10720761 : ℤ), (-10720758 : ℤ), (-6485083 : ℤ), (-6485080 : ℤ), (25394764 : ℤ), (25394767 : ℤ), (64972422 : ℤ), (64972425 : ℤ)⟩, (2 : ℤ), (1 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002.length =
      1 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002).length =
      0 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk004Part002).length =
      0 := by
  rfl

end

end TraceEuclidean
