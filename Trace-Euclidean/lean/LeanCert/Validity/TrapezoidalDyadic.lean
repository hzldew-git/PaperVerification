import LeanCert.Validity.IntegrationDyadic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Pure-kernel dyadic certificates for the trapezoidal rule

This module evaluates a composite trapezoidal sum only at rational points.
It is intended to be combined with Mathlib's rigorous second-derivative
error bound.  Unlike interval range integration, point evaluation does not
accumulate a first-order enclosure error over every cell.
-/

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.IntegrationDyadic

namespace LeanCert.Validity.TrapezoidalDyadic

/-- The `k`-th rational point of the uniform `n`-partition of `I`. -/
def trapezoidalPoint (I : IntervalRat) (n k : ℕ) : ℚ :=
  I.lo + k * I.width / n

/-- Dyadic enclosure of an expression at one rational point. -/
def evalDyadicPoint (e : Expr) (x : ℚ) (cfg : DyadicConfig := {}) : IntervalRat :=
  evalDyadic1 e (IntervalRat.singleton x) cfg

/-- Upper endpoint of a certified point enclosure. -/
def evalDyadicPointUpper (e : Expr) (x : ℚ) (cfg : DyadicConfig := {}) : ℚ :=
  (evalDyadicPoint e x cfg).hi

/-- Recursive domain check for a point evaluation. -/
def checkDyadicPointDomain (e : Expr) (x : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  checkDomainValidDyadic e
    (fun _ => IntervalDyadic.ofIntervalRat (IntervalRat.singleton x) cfg.precision) cfg

/-- Domain check for every point in a composite trapezoidal sum. -/
def checkTrapezoidalDomains (e : Expr) (I : IntervalRat) (n : ℕ)
    (cfg : DyadicConfig := {}) : Bool :=
  checkDyadicPointDomain e I.lo cfg &&
    checkDyadicPointDomain e I.hi cfg &&
    (List.range (n - 1)).all fun k =>
      checkDyadicPointDomain e (trapezoidalPoint I n (k + 1)) cfg

/-- Rational upper enclosure of the composite trapezoidal sum. -/
def trapezoidalUpperDyadic (e : Expr) (I : IntervalRat) (n : ℕ)
    (cfg : DyadicConfig := {}) : ℚ :=
  I.width / n *
    ((evalDyadicPointUpper e I.lo cfg + evalDyadicPointUpper e I.hi cfg) / 2 +
      ∑ k ∈ Finset.range (n - 1),
        evalDyadicPointUpper e (trapezoidalPoint I n (k + 1)) cfg)

/-- A full checked upper certificate, including the analytic error allowance. -/
def checkTrapezoidalUpperDyadicFull (e : Expr) (I : IntervalRat) (n : ℕ)
    (secondDerivBound target : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  checkTrapezoidalDomains e I n cfg &&
    decide (trapezoidalUpperDyadic e I n cfg +
      I.width ^ 3 * secondDerivBound / (12 * n ^ 2) ≤ target)

private theorem eval_dyadic_point_mem (e : Expr) (x : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hdom : checkDyadicPointDomain e x cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ∈ evalDyadicPoint e x cfg := by
  have hdom' : evalDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat (IntervalRat.singleton x) cfg.precision) cfg :=
    checkDomainValidDyadic_correct _ _ _ hdom
  have henv : envMemDyadic (fun _ => (x : ℝ))
      (fun _ => IntervalDyadic.ofIntervalRat (IntervalRat.singleton x) cfg.precision) := by
    intro i
    exact IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton x) cfg.precision hprec
  have h := evalIntervalDyadic_correct_of_domain e _ _ henv cfg hprec hdom'
  exact IntervalDyadic.mem_toIntervalRat.mpr h

private theorem eval_dyadic_point_le_upper (e : Expr) (x : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hdom : checkDyadicPointDomain e x cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ≤ (evalDyadicPointUpper e x cfg : ℝ) :=
  (eval_dyadic_point_mem e x cfg hprec hdom).2

/-- The mathematical trapezoidal sum is below the checked dyadic upper endpoint. -/
theorem trapezoidal_integral_le_upper_dyadic (e : Expr) (I : IntervalRat)
    (n : ℕ) (hn : 0 < n) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkTrapezoidalDomains e I n cfg = true) :
    trapezoidal_integral (fun x => Expr.eval (fun _ => x) e) n I.lo I.hi ≤
      (trapezoidalUpperDyadic e I n cfg : ℝ) := by
  simp only [checkTrapezoidalDomains, Bool.and_eq_true] at hcheck
  obtain ⟨⟨hlo, hhi⟩, hinterior⟩ := hcheck
  rw [List.all_eq_true] at hinterior
  have hlo' := eval_dyadic_point_le_upper e I.lo cfg hprec hlo
  have hhi' := eval_dyadic_point_le_upper e I.hi cfg hprec hhi
  have hinterior' (k : ℕ) (hk : k ∈ Finset.range (n - 1)) :
      Expr.eval (fun _ => ((trapezoidalPoint I n (k + 1) : ℚ) : ℝ)) e ≤
        (evalDyadicPointUpper e (trapezoidalPoint I n (k + 1)) cfg : ℝ) := by
    apply eval_dyadic_point_le_upper e _ cfg hprec
    apply hinterior
    simpa using hk
  unfold trapezoidal_integral trapezoidalUpperDyadic
  push_cast
  have hscale : 0 ≤ ((I.hi : ℝ) - I.lo) / n := by
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast I.le)) (Nat.cast_nonneg n)
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - I.lo := by
    simp [IntervalRat.width]
  rw [hwidth]
  apply mul_le_mul_of_nonneg_left _ hscale
  apply add_le_add
  · linarith
  · apply Finset.sum_le_sum
    intro k hk
    simpa [trapezoidalPoint, IntervalRat.width] using hinterior' k hk

/-- Extract both the point-sum bound and its rational error allowance from a full check. -/
theorem trapezoidal_integral_add_error_le_of_check (e : Expr) (I : IntervalRat)
    (n : ℕ) (hn : 0 < n) (secondDerivBound target : ℚ)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (hcheck : checkTrapezoidalUpperDyadicFull e I n secondDerivBound target cfg = true) :
    trapezoidal_integral (fun x => Expr.eval (fun _ => x) e) n I.lo I.hi +
        (I.width : ℝ) ^ 3 * (secondDerivBound : ℝ) / (12 * (n : ℝ) ^ 2) ≤
      (target : ℝ) := by
  simp only [checkTrapezoidalUpperDyadicFull, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have htrap := trapezoidal_integral_le_upper_dyadic e I n hn cfg hprec hcheck.1
  have hcheckReal :
      ((trapezoidalUpperDyadic e I n cfg +
        I.width ^ 3 * secondDerivBound / (12 * n ^ 2) : ℚ) : ℝ) ≤ (target : ℝ) := by
    exact_mod_cast hcheck.2
  push_cast at hcheckReal
  calc
    (trapezoidal_integral (fun x => Expr.eval (fun _ => x) e) n I.lo I.hi +
        (I.width : ℝ) ^ 3 * (secondDerivBound : ℝ) / (12 * (n : ℝ) ^ 2) : ℝ)
        ≤ ((trapezoidalUpperDyadic e I n cfg : ℝ) +
          (I.width : ℝ) ^ 3 * (secondDerivBound : ℝ) / (12 * (n : ℝ) ^ 2) : ℝ) :=
      by
        simpa [add_comm] using (add_le_add_right htrap
          ((I.width : ℝ) ^ 3 * (secondDerivBound : ℝ) / (12 * (n : ℝ) ^ 2)))
    _ ≤ (target : ℝ) := hcheckReal

end LeanCert.Validity.TrapezoidalDyadic
