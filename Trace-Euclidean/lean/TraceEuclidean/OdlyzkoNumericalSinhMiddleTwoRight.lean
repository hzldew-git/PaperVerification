import TraceEuclidean.OdlyzkoNumericalSinhMiddleTwoRightA
import TraceEuclidean.OdlyzkoNumericalSinhMiddleTwoRightB

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_middle_two_right_upper :
    (∫ x in (9 / 4 : ℝ)..(17 / 6 : ℝ), stableSinhFunction x) ≤ 1305273 / 10000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have hiA : IntervalIntegrable stableSinhFunction volume (9 / 4 : ℝ) (61 / 24 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (9 / 4 : ℝ) ≤ 61 / 24)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hiB : IntervalIntegrable stableSinhFunction volume (61 / 24 : ℝ) (17 / 6 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (61 / 24 : ℝ) ≤ 17 / 6)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hiA hiB]
  linarith [sinh_middle_two_right_a_upper, sinh_middle_two_right_b_upper]

end
end TraceEuclidean.OdlyzkoNumerical
