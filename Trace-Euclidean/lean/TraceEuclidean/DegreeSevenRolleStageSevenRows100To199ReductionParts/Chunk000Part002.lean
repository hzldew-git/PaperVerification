import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 2 for Stage Five rows 100 through 109. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (0 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24228505 : ℤ), (-24228502 : ℤ), (-12955672 : ℤ), (-12955669 : ℤ), (-3523210 : ℤ), (-3523207 : ℤ), (3197122 : ℤ), (3197125 : ℤ), (13397272 : ℤ), (13397275 : ℤ), (67254397 : ℤ), (67254400 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, -1, 0, 9, 3, -9, -3, 1], [-1, 1], [0, 1, 1, -8, -11, -2, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (1 : ℤ), (-2 : ℤ), (16777216 : ℤ), (-24741750 : ℤ), (-24741747 : ℤ), (-9492534 : ℤ), (-9492531 : ℤ), (-7450426 : ℤ), (-7450423 : ℤ), (3980795 : ℤ), (3980798 : ℤ), (13603407 : ℤ), (13603410 : ℤ), (67241912 : ℤ), (67241915 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24619602 : ℤ), (-24619599 : ℤ), (-11457887 : ℤ), (-11457884 : ℤ), (-4574485 : ℤ), (-4574482 : ℤ), (2638745 : ℤ), (2638748 : ℤ), (13914501 : ℤ), (13914504 : ℤ), (67240131 : ℤ), (67240134 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, -1, 1, 9, 3, -9, -3, 1], [0, 1], [-1, 1, 9, 3, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24491195 : ℤ), (-24491192 : ℤ), (-12498318 : ℤ), (-12498315 : ℤ), (-1300134 : ℤ), (-1300131 : ℤ), (-2 : ℤ), (2 : ℤ), (14192703 : ℤ), (14192706 : ℤ), (67238349 : ℤ), (67238352 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 1, 9, 3, -9, -3, 1], [1, 1], [0, 0, 1, 8, -5, -4, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (2 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-24967353 : ℤ), (-24967350 : ℤ), (-9048664 : ℤ), (-9048661 : ℤ), (-6641060 : ℤ), (-6641057 : ℤ), (2197199 : ℤ), (2197202 : ℤ), (14375441 : ℤ), (14375444 : ℤ), (67225840 : ℤ), (67225843 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-24854096 : ℤ), (-24854093 : ℤ), (-11029451 : ℤ), (-11029448 : ℤ), (-2819249 : ℤ), (-2819246 : ℤ), (-2 : ℤ), (2 : ℤ), (14620145 : ℤ), (14620148 : ℤ), (67224056 : ℤ), (67224059 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, 2, 9, 3, -9, -3, 1], [0, 1], [0, 2, 9, 3, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (3 : ℤ), (9 : ℤ), (3 : ℤ), (0 : ℤ), (16777216 : ℤ), (-25180434 : ℤ), (-25180431 : ℤ), (-8812329 : ℤ), (-8812326 : ℤ), (-5088601 : ℤ), (-5088598 : ℤ), (-2 : ℤ), (2 : ℤ), (15013030 : ℤ), (15013033 : ℤ), (67209739 : ℤ), (67209742 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002.length =
      7 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk000Part002).length =
      0 := by
  rfl

end

end TraceEuclidean
