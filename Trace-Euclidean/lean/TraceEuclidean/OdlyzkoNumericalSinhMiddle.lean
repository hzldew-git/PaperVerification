import TraceEuclidean.OdlyzkoNumericalSinhMiddleOneLeft
import TraceEuclidean.OdlyzkoNumericalSinhMiddleOneRight
import TraceEuclidean.OdlyzkoNumericalSinhMiddleTwoLeft
import TraceEuclidean.OdlyzkoNumericalSinhMiddleTwoRight
import TraceEuclidean.OdlyzkoNumericalSinhMiddleThree

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_core_middle_upper :
    (∫ x in (1 / 2 : ℝ)..(4 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 694664 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have h1a := sinh_middle_one_left_upper
  have h1b := sinh_middle_one_right_upper
  have hi1a : IntervalIntegrable stableSinhFunction volume (1 / 2 : ℝ) (13 / 12) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 13 / 12)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi1b : IntervalIntegrable stableSinhFunction volume (13 / 12 : ℝ) (5 / 3) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (13 / 12 : ℝ) ≤ 5 / 3)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h1 : (∫ x in (1 / 2 : ℝ)..(5 / 3 : ℝ), stableSinhFunction x) ≤
      225221 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1a hi1b]
    linarith
  have h2a := sinh_middle_two_left_upper
  have h2b := sinh_middle_two_right_upper
  have hi2a : IntervalIntegrable stableSinhFunction volume (5 / 3 : ℝ) (9 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (5 / 3 : ℝ) ≤ 9 / 4)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi2b : IntervalIntegrable stableSinhFunction volume (9 / 4 : ℝ) (17 / 6) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (9 / 4 : ℝ) ≤ 17 / 6)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have h2 : (∫ x in (5 / 3 : ℝ)..(17 / 6 : ℝ), stableSinhFunction x) ≤
      272119 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi2a hi2b]
    linarith
  have h3 := sinh_middle_three_upper
  have hcont : ContinuousOn stableSinhFunction (Set.Icc (1 / 2 : ℝ) 4) :=
    hc2open.continuousOn.mono (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hi1 : IntervalIntegrable stableSinhFunction volume (1 / 2 : ℝ) (5 / 3) :=
    hi1a.trans hi1b
  have hi2 : IntervalIntegrable stableSinhFunction volume (5 / 3 : ℝ) (17 / 6) :=
    hi2a.trans hi2b
  have hi3 : IntervalIntegrable stableSinhFunction volume (17 / 6 : ℝ) 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (17 / 6 : ℝ) ≤ 4)]
    exact hcont.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have h12 : (∫ x in (1 / 2 : ℝ)..(17 / 6 : ℝ), stableSinhFunction x) ≤
      497340 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    linarith
  have hg : (∫ x in (1 / 2 : ℝ)..(4 : ℝ), stableSinhFunction x) ≤
      694664 / 1000000 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3]
    linarith
  calc
    (∫ x in (1 / 2 : ℝ)..(4 : ℝ),
        (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) =
        ∫ x in (1 / 2 : ℝ)..(4 : ℝ), stableSinhFunction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (1 / 2 : ℝ) 4 := by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 4)] at hx
        exact hx
      exact (eval_stableSinhIntegrand x (lt_of_lt_of_le (by norm_num) hx'.1)
        (by linarith [hx'.2])).symm
    _ ≤ 694664 / 1000000 := hg

end
end TraceEuclidean.OdlyzkoNumerical
