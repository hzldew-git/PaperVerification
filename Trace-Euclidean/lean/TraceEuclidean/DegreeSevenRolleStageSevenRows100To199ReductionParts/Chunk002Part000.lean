import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 0 for Stage Five rows 120 through 129. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (3 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28544891 : ℤ), (-28544888 : ℤ), (-7252338 : ℤ), (-7252335 : ℤ), (-2 : ℤ), (2 : ℤ), (3261665 : ℤ), (3261668 : ℤ), (8354609 : ℤ), (8354612 : ℤ), (67322360 : ℤ), (67322363 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 3, 4, -9, -3, 1], [0, 1], [0, -1, 3, 4, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27950200 : ℤ), (-27950197 : ℤ), (-9371938 : ℤ), (-9371935 : ℤ), (-2 : ℤ), (2 : ℤ), (5883237 : ℤ), (5883240 : ℤ), (7328720 : ℤ), (7328723 : ℤ), (67251586 : ℤ), (67251589 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (4 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28126278 : ℤ), (-28126275 : ℤ), (-8207445 : ℤ), (-8207442 : ℤ), (-2 : ℤ), (2 : ℤ), (2517146 : ℤ), (2517149 : ℤ), (9720565 : ℤ), (9720568 : ℤ), (67237417 : ℤ), (67237420 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 4, 4, -9, -3, 1], [0, 1], [0, -1, 4, 4, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-2 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27481901 : ℤ), (-27481898 : ℤ), (-10266874 : ℤ), (-10266871 : ℤ), (-2 : ℤ), (2 : ℤ), (4214865 : ℤ), (4214868 : ℤ), (9509159 : ℤ), (9509162 : ℤ), (67166156 : ℤ), (67166159 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -2, 5, 4, -9, -3, 1], [0, 1], [0, -2, 5, 4, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-1 : ℤ), (-1 : ℤ), (16777216 : ℤ), (-27732732 : ℤ), (-27732729 : ℤ), (-7614827 : ℤ), (-7614824 : ℤ), (-4069166 : ℤ), (-4069163 : ℤ), (5673070 : ℤ), (5673073 : ℤ), (9731405 : ℤ), (9731408 : ℤ), (67153654 : ℤ), (67153657 : ℤ)⟩, (1 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (-1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-27675866 : ℤ), (-27675863 : ℤ), (-9181268 : ℤ), (-9181265 : ℤ), (-2 : ℤ), (2 : ℤ), (2064194 : ℤ), (2064197 : ℤ), (10782478 : ℤ), (10782481 : ℤ), (67151868 : ℤ), (67151871 : ℤ)⟩, (0 : ℤ), (0 : ℤ), [.reducible ⟨[0, 0, -1, 5, 4, -9, -3, 1], [0, 1], [0, -1, 5, 4, -9, -3, 1], 1, 6⟩]⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (5 : ℤ), (1 : ℤ), (0 : ℤ), (16777216 : ℤ), (-28037981 : ℤ), (-28037978 : ℤ), (-5061659 : ℤ), (-5061656 : ℤ), (-3228977 : ℤ), (-3228974 : ℤ), (-2 : ℤ), (2 : ℤ), (12346800 : ℤ), (12346803 : ℤ), (67123221 : ℤ), (67123224 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000.length =
      7 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000).length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk002Part000).length =
      0 := by
  rfl

end

end TraceEuclidean
