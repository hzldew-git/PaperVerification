/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.FinSumDyadic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Certified Euler–Mascheroni Constant Bounds

Fully machine-checked bounds for `Real.eulerMascheroniConstant`:

  0.5772151 ≤ γ ≤ 0.5772162      (width 1.1e-6; true value γ = 0.5772156649...)

**Sorry-free.** The lower bound used by the Trace-Euclidean development is a
kernel proof. It evaluates only `harmonic 1024` and uses a monotone midpoint
correction. The independent upper bound retains the older `native_decide`
certificate at `N = 2^20`.

## Proof

For the lower bound, use the corrected sequence

  harmonic n - log n - 1 / (2n),

which increases to `γ`. At `n = 1024`, the exact rational lower bound for the
harmonic number and Mathlib's upper bound for `log 2` give `γ ≥ 0.5772151`.

For the independent upper bound, use Mathlib's strict estimate at `N = 2^20`:

  eulerMascheroniSeq N < γ < eulerMascheroniSeq' N

where `eulerMascheroniSeq N = harmonic N - log (N+1)` and
`eulerMascheroniSeq' N = harmonic N - log N`. The sandwich gap is
`log (1 + 1/N) ≈ 9.5e-7`, which dictates the achievable width. Ingredients:

1. **Upper-bound harmonic number.** `harmonic (2^20)` is enclosed above by the
   reflective dyadic sum evaluator (`LeanCert.Engine.FinSumDyadic`) with the
   summand `1/k` expressed as `Expr.inv (Expr.var 0)`, at precision `-80`
   (accumulated outward-rounding error ≤ `2^20 · 2^(-79)` ≈ `2e-18`, far below
   the `4e-11` checker margins):

     14.4401597529 ≤ harmonic (2^20) ≤ 14.4401597530

2. **Logarithm.** `N = 2^20` makes `log N = 20 * log 2`, discharged by
   Mathlib's `Real.log_two_gt_d9`.
-/

namespace EulerMascheroni

open Real LeanCert.Core LeanCert.Engine

/-! ### Internal setup: summand expression, config, truncation index -/

/-- The harmonic summand `1/k` as a LeanCert expression (`var 0` = summation
index). -/
def body : Expr := Expr.inv (Expr.var 0)

/-- 80-bit dyadic precision. The summand is rational, so `taylorDepth` is
inert. -/
def cfg : DyadicConfig := { precision := -80 }

/-- Truncation index `N = 2^20`, chosen so that `log N = 20 * log 2` reduces
to Mathlib's decimal `log 2` bounds. -/
def N : ℕ := 2 ^ 20

/-! ### Bridge: Mathlib's `harmonic` as a `FinSumDyadic` sum -/

/-- `harmonic n` is the semantic sum that `finSumDyadic body 1 n` encloses. -/
theorem harmonic_eq_finsum (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, Expr.eval (sumBodyRealEnv k) body := by
  simp only [body, Expr.eval, sumBodyRealEnv]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)),
      harmonic_succ, ← ih]
    push_cast
    ring

/-! ### Kernel lower bound via a midpoint correction -/

/-- The midpoint-corrected harmonic sequence, indexed from `1`. -/
noncomputable def midpointSeq (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ))

/-- A strict logarithmic bound which makes the midpoint sequence increasing. -/
private lemma log_succ_div_lt (n : ℕ) (hn : 0 < n) :
    Real.log ((n + 1 : ℝ) / n) <
      1 / (2 * (n : ℝ)) + 1 / (2 * (n + 1 : ℝ)) := by
  let y : ℝ := 1 / (2 * (n : ℝ)) + 1 / (2 * (n + 1 : ℝ))
  have hy : 0 ≤ y := by positivity
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.quadratic_le_exp_of_nonneg hy)
  field_simp
  nlinarith

private lemma strictMono_midpointSeq : StrictMono midpointSeq := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hn : 0 < n + 1 := by omega
  have hlog := log_succ_div_lt (n + 1) hn
  have hlog' :
      Real.log (n + 2 : ℝ) - Real.log (n + 1 : ℝ) <
        1 / (2 * (n + 1 : ℝ)) + 1 / (2 * (n + 2 : ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    convert hlog using 1 <;> push_cast <;> ring
  have hharm :
      (harmonic (n + 2) : ℝ) =
        (harmonic (n + 1) : ℝ) + 1 / (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    ring
  rw [midpointSeq, midpointSeq]
  rw [show n + 1 + 1 = n + 2 by omega, hharm]
  push_cast at hlog' ⊢
  ring_nf at hlog' ⊢
  have hhalf :
      (2 + (n : ℝ))⁻¹ - (4 + (n : ℝ) * 2)⁻¹ = (4 + (n : ℝ) * 2)⁻¹ := by
    field_simp
    ring
  linarith [hhalf]

private lemma tendsto_midpointSeq :
    Filter.Tendsto midpointSeq Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hbase := Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
  have hcorr :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have h := hbase.sub hcorr
  convert h using 1
  · ext n
    simp only [Function.comp_apply, midpointSeq]
    push_cast
    field_simp
  · ring

private theorem midpointSeq_le_gamma (n : ℕ) :
    midpointSeq n ≤ Real.eulerMascheroniConstant :=
  strictMono_midpointSeq.monotone.ge_of_tendsto tendsto_midpointSeq n

/-- Exact kernel-checked rational lower bound for `harmonic 1024`. -/
theorem harmonic_1024_ge :
    (75091756722 / 10000000000 : ℝ) ≤ (harmonic 1024 : ℝ) := by
  set_option maxRecDepth 100000 in
    norm_num [harmonic, Finset.sum_range_succ]

/-- Certified lower bound `γ ≥ 0.5772151`, with no native-code axiom. -/
theorem gamma_lower : (0.5772151 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hmid := midpointSeq_le_gamma 1023
  have hH := harmonic_1024_ge
  have hlog : Real.log (1024 : ℝ) < 10 * 0.6931471808 := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  rw [midpointSeq] at hmid
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hmid
  norm_num at ⊢
  linarith [hH]

/-! ### Verified upper harmonic-number enclosure (`native_decide`) -/

/-- Upper bound `harmonic (2^20) ≤ 14.4401597530` (margin `6.2e-11`). -/
theorem harmonic_N_le :
    (harmonic N : ℝ) ≤ (((144401597530 / 10 ^ 10 : ℚ)) : ℝ) := by
  rw [harmonic_eq_finsum]
  exact verify_finsum_upper_full_checked body 1 N
    (144401597530 / 10 ^ 10) cfg (by norm_num [cfg]) (by native_decide)

/-! ### Logarithm bounds at `N = 2^20` -/

theorem log_N_eq : Real.log (N : ℝ) = 20 * Real.log 2 := by
  have h : (N : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by norm_num [N]
  rw [h, Real.log_pow]
  norm_num

/-- `log (N + 1) ≤ 20 * log 2 + 1/N` via `log x ≤ x - 1`. -/
theorem log_N_succ_le :
    Real.log ((N : ℝ) + 1) ≤ 20 * Real.log 2 + 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by norm_num [N]
  have hsplit : Real.log ((N : ℝ) + 1)
      = Real.log (N : ℝ) + Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlog1p : Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ ((N : ℝ) + 1) / (N : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
    field_simp
    ring
  rw [hsplit, log_N_eq]
  linarith [hfrac ▸ hlog1p]

/-! ### The certified γ upper bound and combined interface -/

/-- Certified upper bound: γ ≤ 0.5772162.

From `γ < eulerMascheroniSeq' N`:
`γ < harmonic N - log N ≤ 14.4401597530 - 20·0.6931471803
   = 0.5772161470 ≤ 0.5772162`. -/
theorem gamma_upper : Real.eulerMascheroniConstant ≤ (0.5772162 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  have hN0 : N ≠ 0 := by norm_num [N]
  rw [Real.eulerMascheroniSeq', if_neg hN0] at h
  -- h : γ < (harmonic N : ℝ) - log (N : ℝ)
  have hlog : (13.862943606 : ℝ) < Real.log (N : ℝ) := by
    rw [log_N_eq]
    linarith [Real.log_two_gt_d9]
  have hH := harmonic_N_le
  have hq : (((144401597530 / 10 ^ 10 : ℚ)) : ℝ) = 144401597530 / 10 ^ 10 := by
    push_cast
    norm_num
  rw [hq] at hH
  nlinarith [h, hlog, hH]

/-- Combined bounds: γ ∈ [0.5772151, 0.5772162] (width 1.1e-6). -/
theorem gamma_bounds :
    Real.eulerMascheroniConstant ∈ Set.Icc (0.5772151 : ℝ) 0.5772162 :=
  Set.mem_Icc.mpr ⟨gamma_lower, gamma_upper⟩

/-- γ is approximately 0.57721565, to within 5.5e-7. -/
theorem gamma_approx :
    |Real.eulerMascheroniConstant - 0.57721565| ≤ 0.00000055 := by
  have h := gamma_bounds
  rw [Set.mem_Icc] at h
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

end EulerMascheroni
