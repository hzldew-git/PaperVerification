import LeanCert.Validity.RangeDyadic
import LeanCert.Validity.TrapezoidalDyadic
import LeanCert.Core.ExprDerivative

/-!
# Closed numerical certificate data for the  Odlyzko kernel

This module contains only the expressions, rational intervals, and dyadic
configurations used by the kernel checked range and quadrature certificates.
Keeping the data in a separate module lets Lean cache each expensive closed
proof independently.
-/

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine

def q (r : ℚ) : Expr := .const r
def xExpr : Expr := .var 0
def pi : Expr := .namedConst .pi
def t : Expr := .div xExpr (q 4)
def angle : Expr := .mul pi t
def h : Expr :=
  .add
    (.div (.mul (.add (q 2) (.neg t))
      (.add (q 1) (.div (.cos angle) (q 2)))) (q 3))
    (.div (.sin angle) (.mul (q 2) pi))

/-- Cancellation free form of `cosh (x / 2) - H (x / 4)`. -/
def stableNumerator : Expr :=
  .add
    (.mul (q 2) (.mul (.sinh (.div xExpr (q 4))) (.sinh (.div xExpr (q 4)))))
    (.add
      (.div (.mul (.add (q 2) (.neg t))
        (.add (q 1) (.neg (.cos angle)))) (q 6))
      (.div (.add angle (.neg (.sin angle))) (.mul (q 2) pi)))

def stableSinhDenominator : Expr := .sinh xExpr
def stableCoshDenominator : Expr := .add (q 1) (.cosh xExpr)
def stableSinhIntegrand : Expr := .div stableNumerator stableSinhDenominator
def stableCoshIntegrand : Expr := .div stableNumerator stableCoshDenominator
def stableSinhSecond : Expr :=
  Expr.quotientSecond stableNumerator stableSinhDenominator
def stableCoshSecond : Expr :=
  Expr.quotientSecond stableNumerator stableCoshDenominator

def halfX : Expr := .div xExpr (q 2)
def farSinhFirstDenominator : Expr := .mul (q 2) (.sinh halfX)
def farCoshFirstDenominator : Expr := .mul (q 2) (.cosh halfX)
def farSinhIntegrand : Expr :=
  .add (.div (q 1) farSinhFirstDenominator)
    (.neg (.div h stableSinhDenominator))
def farCoshIntegrand : Expr :=
  .add (.div (q 1) farCoshFirstDenominator)
    (.neg (.div h stableCoshDenominator))
def farSinhSecond : Expr :=
  .add (Expr.quotientSecond (q 1) farSinhFirstDenominator)
    (.neg (Expr.quotientSecond h stableSinhDenominator))
def farCoshSecond : Expr :=
  .add (Expr.quotientSecond (q 1) farCoshFirstDenominator)
    (.neg (Expr.quotientSecond h stableCoshDenominator))

def sinhCoreLow : IntervalRat := ⟨1 / 5, 1 / 2, by norm_num⟩
def sinhCoreMiddle : IntervalRat := ⟨1 / 2, 4, by norm_num⟩
def farCore : IntervalRat := ⟨4, 8, by norm_num⟩
def coshCoreNear : IntervalRat := ⟨0, 4, by norm_num⟩

def rangeConfig : DyadicConfig := { precision := -16, taylorDepth := 4 }
def wideRangeConfig : DyadicConfig := { precision := -24, taylorDepth := 10 }
def lowQuadratureConfig : DyadicConfig := { precision := -32, taylorDepth := 10 }
def quadratureConfig : DyadicConfig := { precision := -20, taylorDepth := 14 }

end TraceEuclidean.OdlyzkoNumerical.Certificate
