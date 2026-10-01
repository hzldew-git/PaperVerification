import TraceEuclidean.DegreeSevenFrontierArithmetic

/-! Candidate-reduction subchunk 9 for Stage Five rows 130 through 139. -/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 100000

def degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009 :
    List DegreeSevenFinalEntryCertificate :=
  [
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (15 : ℤ), (7 : ℤ), (0 : ℤ), (16777216 : ℤ), (-23240192 : ℤ), (-23240189 : ℤ), (-11251885 : ℤ), (-11251882 : ℤ), (-7917196 : ℤ), (-7917193 : ℤ), (-2 : ℤ), (2 : ℤ), (19416266 : ℤ), (19416269 : ℤ), (66134413 : ℤ), (66134416 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (15 : ℤ), (7 : ℤ), (1 : ℤ), (16777216 : ℤ), (-23035090 : ℤ), (-23035087 : ℤ), (-13062503 : ℤ), (-13062500 : ℤ), (-4637551 : ℤ), (-4637548 : ℤ), (-1769177 : ℤ), (-1769174 : ℤ), (19513326 : ℤ), (19513329 : ℤ), (66132399 : ℤ), (66132402 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (15 : ℤ), (8 : ℤ), (1 : ℤ), (16777216 : ℤ), (-23569237 : ℤ), (-23569234 : ℤ), (-10247637 : ℤ), (-10247634 : ℤ), (-7552726 : ℤ), (-7552723 : ℤ), (-1338580 : ℤ), (-1338577 : ℤ), (19733075 : ℤ), (19733078 : ℤ), (66116508 : ℤ), (66116511 : ℤ)⟩, (0 : ℤ), (-1 : ℤ), []⟩,
    ⟨⟨(-3 : ℤ), (-9 : ℤ), (4 : ℤ), (15 : ℤ), (9 : ℤ), (2 : ℤ), (16777216 : ℤ), (-23868501 : ℤ), (-23868498 : ℤ), (-9415746 : ℤ), (-9415743 : ℤ), (-6318379 : ℤ), (-6318376 : ℤ), (-3388498 : ℤ), (-3388495 : ℤ), (20033964 : ℤ), (20033967 : ℤ), (66098564 : ℤ), (66098567 : ℤ)⟩, (1 : ℤ), (0 : ℤ), []⟩
  ]

set_option maxHeartbeats 0 in
-- Kernel evaluation checks the exact a0 list and every factorization.
theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009_valid :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009.Forall
      (fun certificate => certificate.check = true) := by
  decide

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009_entry_count :
    degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009.length =
      4 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009_candidate_count :
    (DegreeSevenFinalEntryCertificate.allCandidates
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009).length =
      0 := by
  rfl

theorem degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009_survivor_count :
    (DegreeSevenFinalEntryCertificate.survivorCoefficients
      degreeSevenStageSevenFinalEntryCertificatesRows100To199Chunk003Part009).length =
      0 := by
  rfl

end

end TraceEuclidean
