import TraceEuclidean.OdlyzkoNumericalCoshNear
import TraceEuclidean.OdlyzkoNumericalCoshFar

namespace TraceEuclidean.OdlyzkoNumerical

open MeasureTheory LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic
open LeanCert.Validity.RangeDyadic
open LeanCert.Validity.TrapezoidalDyadic

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

/-- Certified upper enclosure for the compact part of the cosh integral. -/
theorem cosh_core_upper :
    (∫ x in (0 : ℝ)..(8 : ℝ),
      (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2))) ≤ 750029 / 1000000 := by
  have hnear : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      volume 0 4 := by
    exact odlyzkoCoshIntegrand_integrable.intervalIntegrable
  have hfar : IntervalIntegrable
      (fun x : ℝ ↦ (1 - odlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      volume 4 8 := by
    exact odlyzkoCoshIntegrand_integrable.intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hnear hfar]
  linarith [cosh_core_near_upper, cosh_core_far_upper]

end
end TraceEuclidean.OdlyzkoNumerical
