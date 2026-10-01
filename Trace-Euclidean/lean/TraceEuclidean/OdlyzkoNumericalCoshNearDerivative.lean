import TraceEuclidean.OdlyzkoNumericalBase

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Cached derivative bound for Certificate.unitZeroOne. -/
theorem stableCoshSecond_zeroOne_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitZeroOne.lo : ℝ) Certificate.unitZeroOne.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 : ℚ) : ℝ) := by
  have hbound := stableCoshSecond_bound_of_list
    (I := Certificate.unitZeroOne) (cells := Certificate.coshNearZeroOneRangeCells)
    (lower := -1) (upper := 1) (M := 1)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshNearZeroOneRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitOneTwo. -/
theorem stableCoshSecond_oneTwo_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitOneTwo.lo : ℝ) Certificate.unitOneTwo.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := stableCoshSecond_bound_of_list
    (I := Certificate.unitOneTwo) (cells := Certificate.coshNearOneTwoRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshNearOneTwoRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitTwoThree. -/
theorem stableCoshSecond_twoThree_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitTwoThree.lo : ℝ) Certificate.unitTwoThree.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := stableCoshSecond_bound_of_list
    (I := Certificate.unitTwoThree) (cells := Certificate.coshNearTwoThreeRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshNearTwoThreeRange x hx
  norm_num at hbound ⊢
  exact hbound
/-- Cached derivative bound for Certificate.unitThreeFour. -/
theorem stableCoshSecond_threeFour_bound (x : ℝ)
    (hx : x ∈ Set.Icc (Certificate.unitThreeFour.lo : ℝ) Certificate.unitThreeFour.hi) :
    |iteratedDeriv 2 stableCoshFunction x| ≤ ((1 / 4 : ℚ) : ℝ) := by
  have hbound := stableCoshSecond_bound_of_list
    (I := Certificate.unitThreeFour) (cells := Certificate.coshNearThreeFourRangeCells)
    (lower := -1 / 4) (upper := 1 / 4) (M := 1 / 4)
    (cfg := Certificate.wideRangeConfig)
    (by norm_num) (by norm_num)
    (by norm_num [Certificate.wideRangeConfig])
    Certificate.coshNearThreeFourRange x hx
  norm_num at hbound ⊢
  exact hbound

end
end TraceEuclidean.OdlyzkoNumerical
