import TraceEuclidean.DegreeFiveRolleStageFourBase

/-! Generated exact cubic root intervals, Chunk007. -/

namespace TraceEuclidean

set_option linter.style.longLine false

def degreeFiveStageFourEntriesChunk007 :
    List DegreeFiveStageFourEntry :=
  [
    ⟨(0 : ℤ), (-4 : ℤ), (5 : ℤ), ⟨(-475 : ℚ) / 376, (-24 : ℚ) / 19⟩, ⟨(61 : ℚ) / 106, (80 : ℚ) / 139⟩, ⟨(11 : ℚ) / 16, (185 : ℚ) / 269⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-3 : ℤ), ⟨(-27 : ℚ) / 40, (-110 : ℚ) / 163⟩, ⟨(-25 : ℚ) / 61, (-34 : ℚ) / 83⟩, ⟨(77 : ℚ) / 71, (64 : ℚ) / 59⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-2 : ℤ), ⟨(-731 : ℚ) / 905, (-21 : ℚ) / 26⟩, ⟨(-32 : ℚ) / 135, (-9 : ℚ) / 38⟩, ⟨(117 : ℚ) / 112, (70 : ℚ) / 67⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (-1 : ℤ), ⟨(-63 : ℚ) / 71, (-55 : ℚ) / 62⟩, ⟨(-7 : ℚ) / 62, (-8 : ℚ) / 71⟩, ⟨(4095 : ℚ) / 4096, (4097 : ℚ) / 4096⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (0 : ℤ), ⟨(-37 : ℚ) / 39, (-240 : ℚ) / 253⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(240 : ℚ) / 253, (37 : ℚ) / 39⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (1 : ℤ), ⟨(-4097 : ℚ) / 4096, (-4095 : ℚ) / 4096⟩, ⟨(8 : ℚ) / 71, (7 : ℚ) / 62⟩, ⟨(55 : ℚ) / 62, (63 : ℚ) / 71⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (2 : ℤ), ⟨(-70 : ℚ) / 67, (-117 : ℚ) / 112⟩, ⟨(9 : ℚ) / 38, (32 : ℚ) / 135⟩, ⟨(21 : ℚ) / 26, (731 : ℚ) / 905⟩⟩,
    ⟨(0 : ℤ), (-3 : ℤ), (3 : ℤ), ⟨(-64 : ℚ) / 59, (-77 : ℚ) / 71⟩, ⟨(34 : ℚ) / 83, (25 : ℚ) / 61⟩, ⟨(110 : ℚ) / 163, (27 : ℚ) / 40⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (-1 : ℤ), ⟨(-43 : ℚ) / 64, (-45 : ℚ) / 67⟩, ⟨(-16 : ℚ) / 91, (-13 : ℚ) / 74⟩, ⟨(61 : ℚ) / 72, (50 : ℚ) / 59⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (0 : ℤ), ⟨(-55 : ℚ) / 71, (-79 : ℚ) / 102⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(79 : ℚ) / 102, (55 : ℚ) / 71⟩⟩,
    ⟨(0 : ℤ), (-2 : ℤ), (1 : ℤ), ⟨(-50 : ℚ) / 59, (-61 : ℚ) / 72⟩, ⟨(13 : ℚ) / 74, (16 : ℚ) / 91⟩, ⟨(45 : ℚ) / 67, (43 : ℚ) / 64⟩⟩,
    ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), ⟨(-86 : ℚ) / 157, (-23 : ℚ) / 42⟩, ⟨(-1 : ℚ) / 4096, (1 : ℚ) / 4096⟩, ⟨(23 : ℚ) / 42, (86 : ℚ) / 157⟩⟩
  ]

def degreeFiveStageFourExpectedRangesChunk007 :
    List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [
    ((0 : ℤ), (-4 : ℤ), (5 : ℤ), (-2 : ℤ), (-3 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-3 : ℤ), (-1 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (-1 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (0 : ℤ), (0 : ℤ), (4 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (1 : ℤ), (0 : ℤ), (2 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (2 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-3 : ℤ), (3 : ℤ), (-1 : ℤ), (-1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ)),
    ((0 : ℤ), (-2 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ)),
    ((0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact rational sign checks for this generated chunk require deep reduction.
theorem degreeFiveStageFourEntriesChunk007_valid :
    degreeFiveStageFourEntriesChunk007.Forall
      DegreeFiveStageFourEntry.Valid := by
  norm_num [degreeFiveStageFourEntriesChunk007,
    DegreeFiveStageFourEntry.Valid,
    DegreeFiveStageFourEntry.derivativeCoefficients,
    DegreeFiveStageFourEntry.rootIntervals,
    GeneralRationalRootIntervalCertificate.Valid,
    integerPolynomialRationalEval, DensePolynomial.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact Horner interval evaluation for this generated chunk is kernel checked.
theorem degreeFiveStageFourRangesChunk007_checked :
    degreeFiveStageFourEntriesChunk007.map (fun entry =>
      (entry.a4, entry.a3, entry.a2,
        quarticTranslationLowerBound entry.baseCoefficients
          (-10) 10 entry.secondRoot,
        quarticTranslationUpperBound entry.baseCoefficients
          entry.firstRoot entry.thirdRoot)) =
      degreeFiveStageFourExpectedRangesChunk007 := by
  norm_num [degreeFiveStageFourEntriesChunk007,
    degreeFiveStageFourExpectedRangesChunk007,
    DegreeFiveStageFourEntry.baseCoefficients,
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
theorem degreeFiveStageFourPrefixCountChunk007 :
    (degreeFiveStageFourEntriesChunk007.flatMap fun entry =>
      entry.a1Candidates.toList.map fun a1 =>
        (entry.a4, entry.a3, entry.a2, a1)).length = 20 := by
  norm_num [degreeFiveStageFourEntriesChunk007,
    DegreeFiveStageFourEntry.a1Candidates,
    DegreeFiveStageFourEntry.baseCoefficients,
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
