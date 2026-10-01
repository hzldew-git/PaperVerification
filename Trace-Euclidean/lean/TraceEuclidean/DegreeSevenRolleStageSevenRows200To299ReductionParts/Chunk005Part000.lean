import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 0 for Stage Five rows 250 through 259. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (32 : ℤ), (29 : ℤ), (10 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14298336 : ℤ), (-14298333 : ℤ), (-13211769 : ℤ), (-13211766 : ℤ), (-5284899 : ℤ), (-5284896 : ℤ), (30643145 : ℤ), (30643148 : ℤ), (62070481 : ℤ), (62070484 : ℤ)⟩, (2 : ℤ), (1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32278195 : ℤ), (-32278192 : ℤ), (-4295675 : ℤ), (-4295672 : ℤ), (-2 : ℤ), (2 : ℤ), (4223434 : ℤ), (4223437 : ℤ), (9884979 : ℤ), (9884982 : ℤ), (65606863 : ℤ), (65606866 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 1, 8, -9, -3, 1], [0, 1], [0, -1, 1, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31918611 : ℤ), (-31918608 : ℤ), (-6178881 : ℤ), (-6178878 : ℤ), (-2 : ℤ), (2 : ℤ), (6141824 : ℤ), (6141827 : ℤ), (9569420 : ℤ), (9569423 : ℤ), (65527653 : ℤ), (65527656 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (2 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32013598 : ℤ), (-32013595 : ℤ), (-4935765 : ℤ), (-4935762 : ℤ), (-2 : ℤ), (2 : ℤ), (3233615 : ℤ), (3233618 : ℤ), (11345872 : ℤ), (11345875 : ℤ), (65511282 : ℤ), (65511285 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 2, 8, -9, -3, 1], [0, 1], [0, -1, 2, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-4 : ℤ), (1 : ℤ), (16777216 : ℤ), (-31406332 : ℤ), (-31406329 : ℤ), (-9105125 : ℤ), (-9105122 : ℤ), (2948376 : ℤ), (2948379 : ℤ), (7022114 : ℤ), (7022117 : ℤ), (8220079 : ℤ), (8220082 : ℤ), (65462292 : ℤ), (65462295 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31639697 : ℤ), (-31639694 : ℤ), (-6778334 : ℤ), (-6778331 : ℤ), (-2 : ℤ), (2 : ℤ), (4762421 : ℤ), (4762424 : ℤ), (11365586 : ℤ), (11365589 : ℤ), (65431429 : ℤ), (65431432 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -2, 3, 8, -9, -3, 1], [0, 1], [0, -2, 3, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-31739214 : ℤ), (-31739211 : ℤ), (-5612288 : ℤ), (-5612285 : ℤ), (-2 : ℤ), (2 : ℤ), (2615181 : ℤ), (2615184 : ℤ), (12462832 : ℤ), (12462835 : ℤ), (65414895 : ℤ), (65414898 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 3, 8, -9, -3, 1], [0, 1], [0, -1, 3, 8, -9, -3, 1], 1, 6⟩]⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000.length =
      7 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk005Part000).length =
      0 := by
  rfl

end

end TraceEuclidean
