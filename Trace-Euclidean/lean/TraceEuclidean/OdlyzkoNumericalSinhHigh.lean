import TraceEuclidean.OdlyzkoNumericalSinhMiddle
import TraceEuclidean.OdlyzkoNumericalSinhFar

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

theorem sinh_core_high_upper :
    (∫ x in (1 / 2 : ℝ)..(8 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 927640 / 1000000 := by
  have hmiddle : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      volume (1 / 2) 4 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 4)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1)
  have hfar : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      volume 4 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (4 : ℝ) ≤ 8)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 4) hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hmiddle hfar]
  linarith [sinh_core_middle_upper, sinh_core_far_upper]

end
end TraceEuclidean.OdlyzkoNumerical
