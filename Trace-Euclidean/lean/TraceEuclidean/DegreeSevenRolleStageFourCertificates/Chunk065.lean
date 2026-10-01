import TraceEuclidean.DegreeSevenRolleStageFourBase

/-! Generated exact cubic root intervals, Chunk065. -/

namespace TraceEuclidean

set_option linter.style.longLine false

def degreeSevenStageFourEntriesChunk065 :
    List DegreeSevenStageFourEntry :=
  [
    ⟨(0 : ℤ), (-3 : ℤ), (-1 : ℤ), ⟨(-47 : ℚ) / 76, (-34 : ℚ) / 55⟩, ⟨(-6 : ℚ) / 89, (-7 : ℚ) / 104⟩, ⟨(24 : ℚ) / 35, (251 : ℚ) / 366⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (0 : ℤ), ⟨(-55 : ℚ) / 84, (-36 : ℚ) / 55⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(36 : ℚ) / 55, (55 : ℚ) / 84⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (1 : ℤ), ⟨(-251 : ℚ) / 366, (-24 : ℚ) / 35⟩, ⟨(7 : ℚ) / 104, (6 : ℚ) / 89⟩, ⟨(34 : ℚ) / 55, (47 : ℚ) / 76⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (2 : ℤ), ⟨(-97 : ℚ) / 136, (-92 : ℚ) / 129⟩, ⟨(6 : ℚ) / 43, (19 : ℚ) / 136⟩, ⟨(39 : ℚ) / 68, (35 : ℚ) / 61⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (3 : ℤ), ⟨(-31 : ℚ) / 42, (-138 : ℚ) / 187⟩, ⟨(5 : ℚ) / 22, (48 : ℚ) / 211⟩, ⟨(73 : ℚ) / 143, (24 : ℚ) / 47⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (-2 : ℤ), ⟨(-7 : ℚ) / 20, (-78 : ℚ) / 223⟩, ⟨(-17 : ℚ) / 64, (-30 : ℚ) / 113⟩, ⟨(283 : ℚ) / 460, (8 : ℚ) / 13⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (-1 : ℤ), ⟨(-19 : ℚ) / 40, (-85 : ℚ) / 179⟩, ⟨(-13 : ℚ) / 125, (-8 : ℚ) / 77⟩, ⟨(169 : ℚ) / 292, (11 : ℚ) / 19⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (0 : ℤ), ⟨(-54 : ℚ) / 101, (-31 : ℚ) / 58⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(31 : ℚ) / 58, (54 : ℚ) / 101⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (1 : ℤ), ⟨(-11 : ℚ) / 19, (-169 : ℚ) / 292⟩, ⟨(8 : ℚ) / 77, (13 : ℚ) / 125⟩, ⟨(85 : ℚ) / 179, (19 : ℚ) / 40⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (2 : ℤ), ⟨(-8 : ℚ) / 13, (-283 : ℚ) / 460⟩, ⟨(30 : ℚ) / 113, (17 : ℚ) / 64⟩, ⟨(78 : ℚ) / 223, (7 : ℚ) / 20⟩⟩,
    ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), ⟨(-31 : ℚ) / 82, (-48 : ℚ) / 127⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(48 : ℚ) / 127, (31 : ℚ) / 82⟩⟩
  ]

def degreeSevenStageFourExpectedRangesChunk065 :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [
    ((0 : ℤ), (-3 : ℤ), (-1 : ℤ), (0 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), (6 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (3 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (3 : ℤ), (-1 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-2 : ℤ), (0 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (2 : ℤ), (0 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact rational sign checks for this generated chunk require deep reduction.
theorem degreeSevenStageFourEntriesChunk065_valid :
    degreeSevenStageFourEntriesChunk065.Forall
      DegreeSevenStageFourEntry.Valid := by
  norm_num [degreeSevenStageFourEntriesChunk065,
    DegreeSevenStageFourEntry.Valid,
    DegreeSevenStageFourEntry.derivativeCoefficients,
    DegreeSevenStageFourEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact Horner interval evaluation for this generated chunk is kernel checked.
theorem degreeSevenStageFourRangesChunk065_checked :
    degreeSevenStageFourEntriesChunk065.map (fun entry =>
      (entry.a6, entry.a5, entry.a4,
        quarticTranslationLowerBound entry.baseCoefficients
          (-16) 16 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot)) =
      degreeSevenStageFourExpectedRangesChunk065 := by
  norm_num [degreeSevenStageFourEntriesChunk065,
    degreeSevenStageFourExpectedRangesChunk065,
    DegreeSevenStageFourEntry.baseCoefficients,
    quarticTranslationLowerBound, quarticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The finite candidate count is reduced by the Lean kernel.
theorem degreeSevenStageFourPrefixCountChunk065 :
    (degreeSevenStageFourEntriesChunk065.flatMap fun entry =>
      entry.a3Candidates.toList.map fun a3 =>
        (entry.a6, entry.a5, entry.a4, a3)).length = 24 := by
  norm_num [degreeSevenStageFourEntriesChunk065,
    DegreeSevenStageFourEntry.a3Candidates,
    DegreeSevenStageFourEntry.baseCoefficients,
    quarticTranslationCandidates, integerIcc,
    quarticTranslationLowerBound, quarticTranslationUpperBound,
    integerPolynomialRootIntervalEval,
    integerPolynomialIntervalEval,
    denseRationalPolynomialIntervalEval,
    RationalRootInterval.toIntervalRat,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4, min_def, max_def, Int.toNat]

end TraceEuclidean
