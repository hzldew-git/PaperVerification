import TraceEuclidean.OdlyzkoQuadratureLeafData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.TrapezoidalDyadic

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The closed interval computation exceeds Lean's default elaboration budget.
theorem coshNearTwoThreeAQuadrature : checkTrapezoidalUpperDyadicFull
    stableCoshIntegrand unitTwoThreeA 32 (1 / 4) (95540846389 / 1000000000000)
    quadrature20Depth12 = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
