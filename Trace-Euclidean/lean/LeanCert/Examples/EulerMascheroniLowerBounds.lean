/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Pure-kernel lower bounds for the Euler--Mascheroni constant

The bounds in this module use an exact rational evaluation of `harmonic 1024`
and a monotone midpoint correction.  They are separated from the independent
large finite-sum upper certificate so downstream proofs can import a wholly
kernel-checked dependency.
-/

namespace EulerMascheroni

open Real

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
      (2 + (n : ℝ))⁻¹ - (4 + (n : ℝ) * 2)⁻¹ =
        (4 + (n : ℝ) * 2)⁻¹ := by
    field_simp
    ring
  linarith [hhalf]

private lemma tendsto_midpointSeq :
    Filter.Tendsto midpointSeq Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hbase := Real.tendsto_harmonic_sub_log.comp
    (Filter.tendsto_add_atTop_nat 1)
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

/-- Certified lower bound `γ ≥ 0.5772151`. -/
theorem gamma_lower : (0.5772151 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hmid := midpointSeq_le_gamma 1023
  have hH := harmonic_1024_ge
  have hlog : Real.log (1024 : ℝ) < 10 * 0.6931471808 := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num,
      Real.log_pow]
    linarith [Real.log_two_lt_d9]
  rw [midpointSeq] at hmid
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hmid
  norm_num at ⊢
  linarith [hH]

/-- The sharper lower bound used by the degree-eleven Poitou certificate. -/
theorem gamma_lower_strong :
    (57721558 / 100000000 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hmid := midpointSeq_le_gamma 1023
  have hH := harmonic_1024_ge
  have hlog : Real.log (1024 : ℝ) < 10 * 0.6931471808 := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num,
      Real.log_pow]
    linarith [Real.log_two_lt_d9]
  rw [midpointSeq] at hmid
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hmid
  norm_num at ⊢
  linarith [hH]

end EulerMascheroni
