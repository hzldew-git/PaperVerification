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
/-- Pure kernel certificate for the second derivative on `[1 / 5, 1 / 2]`. -/
theorem lowSinhRange : checkRangeDyadicListFull stableSinhSecond
    (uniformPartition sinhCoreLow 16 (by norm_num)) sinhCoreLow
    (-2) 2 rangeConfig = true := by
  kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
