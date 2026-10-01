import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 0 for Stage Five rows 210 through 219. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (27 : ℤ), (22 : ℤ), (7 : ℤ), (16777216 : ℤ), (-17829673 : ℤ), (-17829670 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-7805337 : ℤ), (-7805334 : ℤ), (-5466265 : ℤ), (-5466262 : ℤ), (27514687 : ℤ), (27514690 : ℤ), (63505210 : ℤ), (63505213 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (6 : ℤ), (29 : ℤ), (26 : ℤ), (9 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-15075101 : ℤ), (-15075098 : ℤ), (-11316697 : ℤ), (-11316694 : ℤ), (-5531302 : ℤ), (-5531299 : ℤ), (28668357 : ℤ), (28668360 : ℤ), (63173365 : ℤ), (63173368 : ℤ)⟩, (1 : ℤ), (1 : ℤ), [.reducible ⟨[1, 9, 26, 29, 6, -9, -3, 1], [1, 1], [1, 8, 18, 11, -5, -4, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31594932 : ℤ), (-31594929 : ℤ), (-4520580 : ℤ), (-4520577 : ℤ), (-2 : ℤ), (2 : ℤ), (4827906 : ℤ), (4827909 : ℤ), (8332656 : ℤ), (8332659 : ℤ), (66096355 : ℤ), (66096358 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000.length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000).length =
      1 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk001Part000).length =
      0 := by
  rfl

end

end TraceEuclidean
