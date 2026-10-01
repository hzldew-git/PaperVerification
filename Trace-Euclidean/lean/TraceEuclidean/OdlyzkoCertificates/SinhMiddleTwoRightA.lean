import TraceEuclidean.OdlyzkoQuadratureLeafData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.TrapezoidalDyadic

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The closed interval computation exceeds Lean's default elaboration budget.
theorem sinhMiddleTwoRightAQuadrature : checkTrapezoidalUpperDyadicFull
    stableSinhIntegrand sinhMiddleTwoRightA 24 (1 / 2) (67479111337 / 1000000000000)
    quadrature20Depth12 = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
