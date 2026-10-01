import TraceEuclidean.OdlyzkoNumericalSinhMiddleThreeA
import TraceEuclidean.OdlyzkoNumericalSinhMiddleThreeB

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_middle_three_upper :
    (∫ x in (17 / 6 : ℝ)..(4 : ℝ), stableSinhFunction x) ≤ 197324 / 1000000 := by
  have hc2open : ContDiffOn ℝ 2 stableSinhFunction (Set.Ioi 0) := by
    change ContDiffOn ℝ 2 (fun x ↦ Expr.eval (fun _ ↦ x) stableSinhIntegrand) (Set.Ioi 0)
    exact Expr.contDiffOn_eval stableSinh_diffSupported 2
      (fun x hx ↦ stableSinh_regular hx)
  have hiA : IntervalIntegrable stableSinhFunction volume (17 / 6 : ℝ) (41 / 12 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (17 / 6 : ℝ) ≤ 41 / 12)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  have hiB : IntervalIntegrable stableSinhFunction volume (41 / 12 : ℝ) (4 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (41 / 12 : ℝ) ≤ 4)]
    exact hc2open.continuousOn.mono
      (fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hiA hiB]
  linarith [sinh_middle_three_a_upper, sinh_middle_three_b_upper]

end
end TraceEuclidean.OdlyzkoNumerical
