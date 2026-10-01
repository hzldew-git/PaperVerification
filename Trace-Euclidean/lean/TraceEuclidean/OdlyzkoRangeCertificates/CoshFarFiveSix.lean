import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

/-- The exact partition used by `coshFarFiveSixRange`.  Naming it lets analytic bridge
theorems reuse the checked list without reducing `uniformPartition` again. -/
def coshFarFiveSixRangeCells : List IntervalRat :=
  uniformPartition unitFiveSix 8 (by norm_num)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kept in its own module so the kernel computation releases memory afterwards.
theorem coshFarFiveSixRange : checkRangeDyadicListFull farCoshSecond
    coshFarFiveSixRangeCells unitFiveSix
    (-1 / 4) (1 / 4) wideRangeConfig = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
