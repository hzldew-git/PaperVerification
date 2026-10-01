import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 7 for Stage Five rows 220 through 229. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-28041061 : ℤ), (-28041058 : ℤ), (-11750686 : ℤ), (-11750683 : ℤ), (-2645239 : ℤ), (-2645236 : ℤ), (3267980 : ℤ), (3267983 : ℤ), (17169928 : ℤ), (17169931 : ℤ), (65140481 : ℤ), (65140484 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, -1, -1, 11, 7, -9, -3, 1], [0, 1], [-1, -1, 11, 7, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27982105 : ℤ), (-27982102 : ℤ), (-12337389 : ℤ), (-12337386 : ℤ), (-2 : ℤ), (2 : ℤ), (973446 : ℤ), (973449 : ℤ), (17349183 : ℤ), (17349186 : ℤ), (65138270 : ℤ), (65138273 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 11, 7, -9, -3, 1], [1, 1], [0, 0, -1, 12, -5, -4, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (0 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-28286208 : ℤ), (-28286205 : ℤ), (-9721881 : ℤ), (-9721878 : ℤ), (-5244633 : ℤ), (-5244630 : ℤ), (3907309 : ℤ), (3907312 : ℤ), (17361301 : ℤ), (17361304 : ℤ), (65125516 : ℤ), (65125519 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-28231472 : ℤ), (-28231469 : ℤ), (-10771846 : ℤ), (-10771843 : ℤ), (-3296044 : ℤ), (-3296041 : ℤ), (2783477 : ℤ), (2783480 : ℤ), (17533987 : ℤ), (17533990 : ℤ), (65123301 : ℤ), (65123304 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, -1, 0, 11, 7, -9, -3, 1], [0, 1], [-1, 0, 11, 7, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-28413110 : ℤ), (-28413107 : ℤ), (-9522790 : ℤ), (-9522787 : ℤ), (-4271768 : ℤ), (-4271765 : ℤ), (2368513 : ℤ), (2368516 : ℤ), (17874472 : ℤ), (17874475 : ℤ), (65106086 : ℤ), (65106089 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28360238 : ℤ), (-28360235 : ℤ), (-10546213 : ℤ), (-10546210 : ℤ), (-1081982 : ℤ), (-1081979 : ℤ), (-2 : ℤ), (2 : ℤ), (18025974 : ℤ), (18025977 : ℤ), (65103865 : ℤ), (65103868 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 1, 11, 7, -9, -3, 1], [0, 1], [0, 1, 11, 7, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28536588 : ℤ), (-28536585 : ℤ), (-9362507 : ℤ), (-9362504 : ℤ), (-2382156 : ℤ), (-2382153 : ℤ), (-2 : ℤ), (2 : ℤ), (18336048 : ℤ), (18336051 : ℤ), (65086609 : ℤ), (65086612 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 2, 11, 7, -9, -3, 1], [2, 1], [0, 0, 1, 5, 1, -5, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (7 : ℤ), (11 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28705637 : ℤ), (-28705634 : ℤ), (-7470230 : ℤ), (-7470227 : ℤ), (-4382746 : ℤ), (-4382743 : ℤ), (-2 : ℤ), (2 : ℤ), (18630701 : ℤ), (18630704 : ℤ), (65069316 : ℤ), (65069319 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007.length =
      8 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007).length =
      5 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk002Part007).length =
      0 := by
  rfl

end

end TraceEuclidean
