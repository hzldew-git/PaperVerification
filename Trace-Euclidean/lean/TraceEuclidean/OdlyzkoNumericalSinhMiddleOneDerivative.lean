import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Certified second derivative bound on the first middle sinh interval. -/
theorem stableSinhSecond_middleOne_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.sinhMiddleOne.lo : ℝ)
      Certificate.sinhMiddleOne.hi) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 : ℚ) : ℝ) := by
  have hbound := stableSinhSecond_bound_of_list
    (I := Certificate.sinhMiddleOne)
    (cells := Certificate.sinhMiddleOneRangeCells)
    (lower := -1) (upper := 1) (M := 1)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.sinhMiddleOne])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhMiddleOneRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
