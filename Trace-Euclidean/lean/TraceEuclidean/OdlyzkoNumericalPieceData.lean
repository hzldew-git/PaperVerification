import TraceEuclidean.OdlyzkoNumericalCertificateData

/-!
# Rational subintervals and configurations for the  Odlyzko certificates

The large trapezoidal checks are split into 128-point pieces.  Their bounds
add to the stated bounds in `OdlyzkoNumerical`; the split keeps each kernel
proof within a predictable memory limit.
-/

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine

/-! The generated certificate modules share this tactic.  Keeping one exported
definition avoids duplicate environment entries when all pieces are imported by
the aggregate modules. -/
elab "odlyzko_kernel_rfl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    Lean.Meta.withTransparency .all goal.applyRfl
  Lean.Elab.Tactic.replaceMainGoal []

def sinhMiddleOne : IntervalRat := ⟨1 / 2, 5 / 3, by norm_num⟩
def sinhMiddleTwo : IntervalRat := ⟨5 / 3, 17 / 6, by norm_num⟩
def sinhMiddleThree : IntervalRat := ⟨17 / 6, 4, by norm_num⟩

def unitZeroOne : IntervalRat := ⟨0, 1, by norm_num⟩
def unitOneTwo : IntervalRat := ⟨1, 2, by norm_num⟩
def unitTwoThree : IntervalRat := ⟨2, 3, by norm_num⟩
def unitThreeFour : IntervalRat := ⟨3, 4, by norm_num⟩
def unitFourFive : IntervalRat := ⟨4, 5, by norm_num⟩
def unitFiveSix : IntervalRat := ⟨5, 6, by norm_num⟩
def unitSixSeven : IntervalRat := ⟨6, 7, by norm_num⟩
def unitSevenEight : IntervalRat := ⟨7, 8, by norm_num⟩

def quadrature20Depth8 : DyadicConfig := { precision := -20, taylorDepth := 8 }
def quadrature20Depth10 : DyadicConfig := { precision := -20, taylorDepth := 10 }
def quadrature20Depth12 : DyadicConfig := { precision := -20, taylorDepth := 12 }
def quadrature20Depth13 : DyadicConfig := { precision := -20, taylorDepth := 13 }
def quadrature20Depth14 : DyadicConfig := { precision := -20, taylorDepth := 14 }
def quadrature19Depth14 : DyadicConfig := { precision := -19, taylorDepth := 14 }

end TraceEuclidean.OdlyzkoNumerical.Certificate
