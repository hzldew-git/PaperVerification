import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

/-- The exact partition used by `coshNearOneTwoRange`.  Naming it lets analytic bridge
theorems reuse the checked list without reducing `uniformPartition` again. -/
def coshNearOneTwoRangeCells : List IntervalRat :=
  uniformPartition unitOneTwo 16 (by norm_num)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kept in its own module so the kernel computation releases memory afterwards.
theorem coshNearOneTwoRange : checkRangeDyadicListFull stableCoshSecond
    coshNearOneTwoRangeCells unitOneTwo
    (-1 / 4) (1 / 4) wideRangeConfig = true := by
  odlyzko_kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
