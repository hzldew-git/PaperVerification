import TraceEuclidean.OdlyzkoLowData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.TrapezoidalDyadic

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kept separate so the kernel computation releases memory afterwards.
theorem lowSinhFourQuadrature : checkTrapezoidalUpperDyadicFull
    stableSinhIntegrand sinhCoreLowFour 32 2 (7608 / 1000000)
    fastLowQuadratureConfig = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
