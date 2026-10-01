import TraceEuclidean.VoightTotalRealityCertificates.SevenChunk2

/-! Generated rational root intervals for at most one hundred rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false
set_option maxRecDepth 100000

def voightRootIntervalsSevenChunk3 :
    List (List RationalRootInterval) :=
  [
    [⟨(-94 : ℚ) / 57, (-61 : ℚ) / 37⟩, ⟨(-85 : ℚ) / 66, (-94 : ℚ) / 73⟩, ⟨(-25 : ℚ) / 31, (-29 : ℚ) / 36⟩, ⟨(4 : ℚ) / 11, (35 : ℚ) / 96⟩, ⟨(38 : ℚ) / 33, (53 : ℚ) / 46⟩, ⟨(107 : ℚ) / 68, (96 : ℚ) / 61⟩, ⟨(191 : ℚ) / 72, (130 : ℚ) / 49⟩]
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Native replay is exact but intentionally has no heartbeat limit.
theorem voightRootIntervalsSevenChunk3_check :
    rootIntervalCertificateBatchCheck 7
      voightPolynomialRowsSevenChunk3 voightRootIntervalsSevenChunk3 = true := by
  native_decide

theorem voightRowsSevenChunk3_splits :
    ∀ row ∈ voightPolynomialRowsSevenChunk3, row.realPolynomial.Splits :=
  splits_of_rootIntervalBatchCheck_eq_true 7
    (certificates := voightRootIntervalsSevenChunk3) voightRootIntervalsSevenChunk3_check

end TraceEuclidean
