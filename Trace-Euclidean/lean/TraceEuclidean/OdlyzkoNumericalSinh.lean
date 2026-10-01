import TraceEuclidean.OdlyzkoNumericalSinhLow
import TraceEuclidean.OdlyzkoNumericalSinhHigh

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Certified upper enclosure for the nonsingular part of the sinh integral. -/
theorem sinh_core_upper :
    (∫ x in (1 / 5 : ℝ)..(8 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 950958 / 1000000 := by
  have hlow : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      volume (1 / 5) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 5) hx.1)
  have hhigh : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      volume (1 / 2) 8 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 8)]
    exact odlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hlow hhigh]
  linarith [sinh_core_low_upper, sinh_core_high_upper]

end
end TraceEuclidean.OdlyzkoNumerical
