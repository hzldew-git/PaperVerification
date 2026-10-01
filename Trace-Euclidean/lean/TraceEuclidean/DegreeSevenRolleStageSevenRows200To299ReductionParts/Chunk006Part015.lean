import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 15 for Stage Five rows 260 through 269. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-28532540 : ℤ), (-28532537 : ℤ), (-10882980 : ℤ), (-10882977 : ℤ), (-3669078 : ℤ), (-3669075 : ℤ), (2211130 : ℤ), (2211133 : ℤ), (19646760 : ℤ), (19646763 : ℤ), (64368112 : ℤ), (64368115 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, -1, 1, 13, 8, -9, -3, 1], [0, 1], [-1, 1, 13, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28479328 : ℤ), (-28479325 : ℤ), (-11605822 : ℤ), (-11605819 : ℤ), (-903224 : ℤ), (-903221 : ℤ), (-2 : ℤ), (2 : ℤ), (19764077 : ℤ), (19764080 : ℤ), (64365702 : ℤ), (64365705 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 1, 13, 8, -9, -3, 1], [0, 1], [0, 1, 13, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-28708082 : ℤ), (-28708079 : ℤ), (-9614969 : ℤ), (-9614966 : ℤ), (-4714698 : ℤ), (-4714695 : ℤ), (1909789 : ℤ), (1909792 : ℤ), (19919761 : ℤ), (19919764 : ℤ), (64349602 : ℤ), (64349605 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28657486 : ℤ), (-28657483 : ℤ), (-10647747 : ℤ), (-10647744 : ℤ), (-1931257 : ℤ), (-1931254 : ℤ), (-2 : ℤ), (2 : ℤ), (20030710 : ℤ), (20030713 : ℤ), (64347185 : ℤ), (64347188 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 2, 13, 8, -9, -3, 1], [2, 1], [0, 0, 1, 6, 1, -5, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28828088 : ℤ), (-28828085 : ℤ), (-9436966 : ℤ), (-9436963 : ℤ), (-3209105 : ℤ), (-3209102 : ℤ), (-2 : ℤ), (2 : ℤ), (20286938 : ℤ), (20286941 : ℤ), (64328626 : ℤ), (64328629 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 3, 13, 8, -9, -3, 1], [0, 1], [0, 3, 13, 8, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (8 : ℤ), (13 : ℤ), (4 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28991886 : ℤ), (-28991883 : ℤ), (-7197873 : ℤ), (-7197870 : ℤ), (-5512678 : ℤ), (-5512675 : ℤ), (-2 : ℤ), (2 : ℤ), (20533817 : ℤ), (20533820 : ℤ), (64310025 : ℤ), (64310028 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015.length =
      6 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows200To299Chunk006Part015).length =
      0 := by
  rfl

end

end TraceEuclidean
