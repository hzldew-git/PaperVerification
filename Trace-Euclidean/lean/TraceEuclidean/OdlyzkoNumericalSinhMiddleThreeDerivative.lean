import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Certified second derivative bound on the third middle sinh interval. -/
theorem stableSinhSecond_middleThree_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.sinhMiddleThree.lo : ℝ)
      Certificate.sinhMiddleThree.hi) :
    |iteratedDeriv 2 stableSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := stableSinhSecond_bound_of_list
    (I := Certificate.sinhMiddleThree)
    (cells := Certificate.sinhMiddleThreeRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.sinhMiddleThree])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhMiddleThreeRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
