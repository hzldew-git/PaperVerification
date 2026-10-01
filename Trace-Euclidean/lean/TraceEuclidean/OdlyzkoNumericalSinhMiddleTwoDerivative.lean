import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Certified second derivative bound on the whole second middle sinh interval. -/
theorem stableSinhSecond_middleTwo_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.sinhMiddleTwo.lo : ℝ)
      Certificate.sinhMiddleTwo.hi) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 / 2 : ℚ) : ℝ) := by
  have hbound := stableSinhSecond_bound_of_list
    (I := Certificate.sinhMiddleTwo)
    (cells := Certificate.sinhMiddleTwoRangeCells)
    (lower := -1 / 2) (upper := 1 / 2) (M := 1 / 2)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.sinhMiddleTwo])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhMiddleTwoRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
