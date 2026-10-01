import TraceEuclidean.OdlyzkoNumericalCertificateData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.TrapezoidalDyadic

elab "kernel_rfl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    Lean.Meta.withTransparency .all goal.applyRfl
  Lean.Elab.Tactic.replaceMainGoal []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Pure kernel trapezoidal certificate for the cosh integrand on `[4, 8]`. -/
theorem farCoshQuadrature : checkTrapezoidalUpperDyadicFull
    farCoshIntegrand farCore 512 1 (229749 / 1000000)
    quadratureConfig = true := by
  kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
