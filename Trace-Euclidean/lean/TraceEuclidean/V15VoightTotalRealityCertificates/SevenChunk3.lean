import TraceEuclidean.V15VoightTotalRealityCertificates.SevenChunk2

/-! Generated rational root intervals for at most one hundred rows. -/

namespace TraceEuclidean

set_option linter.style.longLine false
set_option maxRecDepth 100000

def v15VoightRootIntervalsSevenChunk3 :
    List (List V15RationalRootInterval) :=
  [
    [⟨(-94 : ℚ) / 57, (-61 : ℚ) / 37⟩, ⟨(-85 : ℚ) / 66, (-94 : ℚ) / 73⟩, ⟨(-25 : ℚ) / 31, (-29 : ℚ) / 36⟩, ⟨(4 : ℚ) / 11, (35 : ℚ) / 96⟩, ⟨(38 : ℚ) / 33, (53 : ℚ) / 46⟩, ⟨(107 : ℚ) / 68, (96 : ℚ) / 61⟩, ⟨(191 : ℚ) / 72, (130 : ℚ) / 49⟩]
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Native replay is exact but intentionally has no heartbeat limit.
theorem v15_voightRootIntervalsSevenChunk3_check :
    v15RootIntervalCertificateBatchCheck 7
      v15VoightPolynomialRowsSevenChunk3 v15VoightRootIntervalsSevenChunk3 = true := by
  native_decide

theorem v15_voightRowsSevenChunk3_splits :
    ∀ row ∈ v15VoightPolynomialRowsSevenChunk3, row.realPolynomial.Splits :=
  v15_splits_of_rootIntervalBatchCheck_eq_true 7
    (certificates := v15VoightRootIntervalsSevenChunk3) v15_voightRootIntervalsSevenChunk3_check

end TraceEuclidean
