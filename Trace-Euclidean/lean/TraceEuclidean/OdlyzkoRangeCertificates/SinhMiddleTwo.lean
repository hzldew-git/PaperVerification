import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

/-- The exact partition used by `sinhMiddleTwoRange`.  Naming it lets analytic bridge
theorems reuse the checked list without reducing `uniformPartition` again. -/
def sinhMiddleTwoRangeCells : List IntervalRat :=
  uniformPartition sinhMiddleTwo 16 (by norm_num)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kept in its own module so the kernel computation releases memory afterwards.
theorem sinhMiddleTwoRange : checkRangeDyadicListFull stableSinhSecond
    sinhMiddleTwoRangeCells sinhMiddleTwo
    (-1 / 2) (1 / 2) wideRangeConfig = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
