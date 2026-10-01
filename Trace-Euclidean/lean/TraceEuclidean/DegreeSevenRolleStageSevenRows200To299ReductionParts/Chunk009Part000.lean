import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 0 for Stage Five rows 290 through 299. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (36 : ℤ), (35 : ℤ), (14 : ℤ), (16777216 : ℤ), (-16777218 : ℤ), (-16777214 : ℤ), (-14589096 : ℤ), (-14589093 : ℤ), (-11933884 : ℤ), (-11933881 : ℤ), (-7545722 : ℤ), (-7545719 : ℤ), (33398356 : ℤ), (33398359 : ℤ), (60588967 : ℤ), (60588970 : ℤ)⟩, (2 : ℤ), (2 : ℤ), [.reducible ⟨[2, 14, 35, 36, 8, -9, -3, 1], [1, 1], [2, 12, 23, 13, -5, -4, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-33170059 : ℤ), (-33170056 : ℤ), (-3550737 : ℤ), (-3550734 : ℤ), (-2 : ℤ), (2 : ℤ), (5261979 : ℤ), (5261982 : ℤ), (9398501 : ℤ), (9398504 : ℤ), (65201722 : ℤ), (65201725 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 0, 9, -9, -3, 1], [0, 1], [0, -1, 0, 9, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (9 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-32930157 : ℤ), (-32930154 : ℤ), (-4097439 : ℤ), (-4097436 : ℤ), (-2 : ℤ), (2 : ℤ), (3857289 : ℤ), (3857292 : ℤ), (11208279 : ℤ), (11208282 : ℤ), (65103432 : ℤ), (65103435 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 1, 9, -9, -3, 1], [0, 1], [0, -1, 1, 9, -9, -3, 1], 1, 6⟩]⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000.length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000).length =
      3 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk009Part000).length =
      0 := by
  rfl

end

end TraceEuclidean
