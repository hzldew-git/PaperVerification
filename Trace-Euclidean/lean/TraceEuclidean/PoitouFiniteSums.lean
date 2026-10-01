import LeanCert.Engine.FinSumDyadic
import TraceEuclidean.PoitouSeriesBounds

/-!
# Kernel certificates for the finite part of Poitou's degree-eleven sums

The expressions in this file are rational functions.  `LeanCert` evaluates
them with dyadic interval arithmetic, while the final Boolean certificates are
reduced by the Lean kernel.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open scoped BigOperators
open Finset

namespace TraceEuclidean.PoitouFiniteSums

open LeanCert.Core LeanCert.Engine

elab "poitou_kernel_rfl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    Lean.Meta.withTransparency .all goal.applyRfl
  Lean.Elab.Tactic.replaceMainGoal []

private def horner (x : Expr) : List ℚ → Expr
  | [] => .const 0
  | c :: cs => .add (.const c) (.mul x (horner x cs))

private def upperPolyExpr (x : Expr) : Expr :=
  horner x [0, 4 / 5, -144 / 175, 128 / 105, -512 / 231,
    145920 / 77, -75776 / 15, 1343488 / 75, -3538944 / 55,
    3145728 / 11]

private def lowerPolyExpr (x : Expr) : Expr :=
  horner x [0, 4 / 5, -144 / 175, 128 / 105, -512 / 231,
    4608 / 1001, -14336 / 13, -7602176 / 425, -1572864 / 85]

private def affineIndex (a b : ℚ) : Expr :=
  .add (.mul (.const a) (.var 0)) (.const b)

private def scaledArgument (d : Expr) : Expr :=
  .div (.const (1351 / 2000)) (.pow d 2)

/-- The upper-polynomial terms for odd denominators `7, ..., 301`. -/
def firstFiniteBody : Expr :=
  let d := affineIndex 2 7
  .div (upperPolyExpr (scaledArgument d)) d

/-- Paired upper bounds for `L(y/(2k+5)^2)-L(y/(2k+4)^2)`. -/
def alternatingPairsBody : Expr :=
  let odd := affineIndex 2 5
  let even := affineIndex 2 4
  .sub (upperPolyExpr (scaledArgument odd))
    (lowerPolyExpr (scaledArgument even))

def sumConfig : DyadicConfig := { precision := -128, taylorDepth := 1 }

private theorem firstFiniteBody_eval (k : ℕ) :
    Expr.eval (sumBodyRealEnv k) firstFiniteBody =
      TraceEuclidean.PoitouSeriesBounds.upperPoly
          (TraceEuclidean.PoitouDegreeEleven.poitouY /
            (((2 * k + 7 : ℕ) : ℝ) ^ 2)) /
        ((2 * k + 7 : ℕ) : ℝ) := by
  simp [firstFiniteBody, affineIndex, scaledArgument, upperPolyExpr, horner,
    Expr.eval, sumBodyRealEnv,
    TraceEuclidean.PoitouSeriesBounds.upperPoly,
    TraceEuclidean.PoitouDegreeEleven.poitouY]
  push_cast
  ring

private theorem alternatingPairsBody_eval (k : ℕ) :
    Expr.eval (sumBodyRealEnv k) alternatingPairsBody =
      TraceEuclidean.PoitouSeriesBounds.upperPoly
          (TraceEuclidean.PoitouDegreeEleven.poitouY /
            (((2 * k + 5 : ℕ) : ℝ) ^ 2)) -
        TraceEuclidean.PoitouSeriesBounds.lowerPoly
          (TraceEuclidean.PoitouDegreeEleven.poitouY /
            (((2 * k + 4 : ℕ) : ℝ) ^ 2)) := by
  simp [alternatingPairsBody, affineIndex, scaledArgument, upperPolyExpr,
    lowerPolyExpr, horner, Expr.sub, Expr.eval, sumBodyRealEnv,
    TraceEuclidean.PoitouSeriesBounds.upperPoly,
    TraceEuclidean.PoitouSeriesBounds.lowerPoly,
    TraceEuclidean.PoitouDegreeEleven.poitouY]
  push_cast
  ring

theorem firstFiniteUpper :
    (∑ k ∈ Icc 0 147,
        TraceEuclidean.PoitouSeriesBounds.upperPoly
            (TraceEuclidean.PoitouDegreeEleven.poitouY /
              (((2 * k + 7 : ℕ) : ℝ) ^ 2)) /
          ((2 * k + 7 : ℕ) : ℝ)) ≤
      (((362056 / 100000000 : ℚ)) : ℝ) := by
  have h := verify_finsum_upper_full_checked firstFiniteBody 0 147
    (362056 / 100000000) sumConfig (by norm_num [sumConfig])
      (by poitou_kernel_rfl)
  simpa only [firstFiniteBody_eval] using h

theorem alternatingPairsUpper :
    (∑ k ∈ Icc 1 198,
        (TraceEuclidean.PoitouSeriesBounds.upperPoly
            (TraceEuclidean.PoitouDegreeEleven.poitouY /
              (((2 * k + 5 : ℕ) : ℝ) ^ 2)) -
          TraceEuclidean.PoitouSeriesBounds.lowerPoly
            (TraceEuclidean.PoitouDegreeEleven.poitouY /
              (((2 * k + 4 : ℕ) : ℝ) ^ 2)))) ≤
      (((-853693 / 100000000 : ℚ)) : ℝ) := by
  have h := verify_finsum_upper_full_checked alternatingPairsBody 1 198
    (-853693 / 100000000) sumConfig (by norm_num [sumConfig])
      (by poitou_kernel_rfl)
  simpa only [alternatingPairsBody_eval] using h

end TraceEuclidean.PoitouFiniteSums
