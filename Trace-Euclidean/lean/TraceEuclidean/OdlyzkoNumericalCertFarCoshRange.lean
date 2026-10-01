import TraceEuclidean.OdlyzkoNumericalCertificateData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.RangeDyadic

elab "kernel_rfl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    Lean.Meta.withTransparency .all goal.applyRfl
  Lean.Elab.Tactic.replaceMainGoal []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Pure kernel certificate for the cosh second derivative on `[4, 8]`. -/
theorem farCoshRange : checkRangeDyadicListFull farCoshSecond
    (uniformPartition farCore 32 (by norm_num)) farCore
    (-1) 1 wideRangeConfig = true := by
  kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
