import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

/-- The exact partition used by `sinhMiddleThreeRange`.  Naming it lets analytic bridge
theorems reuse the checked list without reducing `uniformPartition` again. -/
def sinhMiddleThreeRangeCells : List IntervalRat :=
  uniformPartition sinhMiddleThree 16 (by norm_num)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kept in its own module so the kernel computation releases memory afterwards.
theorem sinhMiddleThreeRange : checkRangeDyadicListFull stableSinhSecond
    sinhMiddleThreeRangeCells sinhMiddleThree
    (-1 / 4) (1 / 4) wideRangeConfig = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
