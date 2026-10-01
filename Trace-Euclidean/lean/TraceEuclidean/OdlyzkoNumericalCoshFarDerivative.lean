import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Cached derivative bound for Certificate.unitFourFive. -/
theorem farCoshSecond_fourFive_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitFourFive.lo : ℝ) Certificate.unitFourFive.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farCoshSecond_bound_of_list
    (I := Certificate.unitFourFive) (cells := Certificate.coshFarFourFiveRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshFarFourFiveRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitFiveSix. -/
theorem farCoshSecond_fiveSix_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitFiveSix.lo : ℝ) Certificate.unitFiveSix.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farCoshSecond_bound_of_list
    (I := Certificate.unitFiveSix) (cells := Certificate.coshFarFiveSixRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshFarFiveSixRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitSixSeven. -/
theorem farCoshSecond_sixSeven_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitSixSeven.lo : ℝ) Certificate.unitSixSeven.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farCoshSecond_bound_of_list
    (I := Certificate.unitSixSeven) (cells := Certificate.coshFarSixSevenRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshFarSixSevenRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitSevenEight. -/
theorem farCoshSecond_sevenEight_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitSevenEight.lo : ℝ) Certificate.unitSevenEight.hi) :
    |iteratedDeriv 2 farCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farCoshSecond_bound_of_list
    (I := Certificate.unitSevenEight) (cells := Certificate.coshFarSevenEightRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshFarSevenEightRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
