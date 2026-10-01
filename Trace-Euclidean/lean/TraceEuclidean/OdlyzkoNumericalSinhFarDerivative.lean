import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Cached derivative bound for Certificate.unitFourFive. -/
theorem farSinhSecond_fourFive_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitFourFive.lo : ℝ) Certificate.unitFourFive.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farSinhSecond_bound_of_list
    (I := Certificate.unitFourFive) (cells := Certificate.sinhFarFourFiveRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.unitFourFive])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhFarFourFiveRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitFiveSix. -/
theorem farSinhSecond_fiveSix_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitFiveSix.lo : ℝ) Certificate.unitFiveSix.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farSinhSecond_bound_of_list
    (I := Certificate.unitFiveSix) (cells := Certificate.sinhFarFiveSixRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.unitFiveSix])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhFarFiveSixRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitSixSeven. -/
theorem farSinhSecond_sixSeven_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitSixSeven.lo : ℝ) Certificate.unitSixSeven.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farSinhSecond_bound_of_list
    (I := Certificate.unitSixSeven) (cells := Certificate.sinhFarSixSevenRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.unitSixSeven])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhFarSixSevenRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitSevenEight. -/
theorem farSinhSecond_sevenEight_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitSevenEight.lo : ℝ) Certificate.unitSevenEight.hi) :
    |iteratedDeriv 2 farSinhFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := farSinhSecond_bound_of_list
    (I := Certificate.unitSevenEight) (cells := Certificate.sinhFarSevenEightRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.unitSevenEight])
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.sinhFarSevenEightRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
