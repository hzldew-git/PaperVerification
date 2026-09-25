/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.Statements

/-!
# Nonvanishing of the Dedekind zeta function on `re s > 1`

This module combines the ideal Euler product from `DedekindZeta.Statements`
with the standard nonvanishing criterion for absolutely convergent infinite
products.  It removes the pointwise nonvanishing premise from the
right-half-plane logarithmic-derivative formula.
-/

open NumberField IsDedekindDomain Filter
open scoped Real nonZeroDivisors Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- Every prime-ideal Euler parameter has norm strictly smaller than one on
`re s > 1`. -/
theorem norm_primeIdeal_absNorm_neg_cpow_lt_one {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
  have hNneZero : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
  have hNneOne : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h
    exact v.isPrime.ne_top ((Ideal.absNorm_eq_one_iff).mp h)
  have hNone : 1 < Ideal.absNorm v.asIdeal := by omega
  have hNpos : 0 < Ideal.absNorm v.asIdeal := Nat.zero_lt_of_lt hNone
  rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hNone) (by linarith)

/-- The Dedekind zeta function has no zero in its half-plane of absolute
convergence. -/
theorem dedekindZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by
  let g : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun v => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)
  let δ : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun v => (1 - g v)⁻¹ - 1
  have hg : ∀ v, ‖g v‖ < 1 := by
    intro v
    exact norm_primeIdeal_absNorm_neg_cpow_lt_one K hs v
  have hsumg : Summable (fun v => ‖g v‖) := by
    simpa [g] using summable_primeIdeal_absNorm_neg_cpow K hs
  have hden : ∀ v, 1 - g v ≠ 0 := by
    intro v hzero
    have hone : g v = 1 := (sub_eq_zero.mp hzero).symm
    have hnorm := congrArg norm hone
    rw [norm_one] at hnorm
    linarith [hg v]
  have hg0 : Tendsto g cofinite (𝓝 0) := hsumg.of_norm.tendsto_cofinite_zero
  have hinv : Tendsto (fun v => (1 - g v)⁻¹) cofinite (𝓝 1) := by
    have hsub : Tendsto (fun v => 1 - g v) cofinite (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hg0
    simpa using hsub.inv₀ (by norm_num)
  have hsumMul : Summable (fun v => ‖g v‖ * ‖(1 - g v)⁻¹‖) := by
    refine Summable.mul_tendsto_const (c := (1 : ℝ))
      (by simpa only [norm_norm] using hsumg) ?_
    simpa using hinv.norm
  have hsumδ : Summable (fun v => ‖δ v‖) := by
    refine hsumMul.congr (fun v => ?_)
    have hidentity : (1 - g v)⁻¹ - 1 = g v * (1 - g v)⁻¹ := by
      field_simp [hden v]
      ring
    change ‖g v‖ * ‖(1 - g v)⁻¹‖ = ‖(1 - g v)⁻¹ - 1‖
    rw [hidentity, norm_mul]
  have hnonzero : ∏' v, (1 + δ v) ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable ?_ hsumδ
    intro v
    have hfactor : 1 + δ v = (1 - g v)⁻¹ := by simp [δ]
    rw [hfactor]
    exact inv_ne_zero (hden v)
  have hEuler := hasProd_primeIdeal_eulerFactors K hs
  rw [← hEuler.tprod_eq]
  simpa [g, δ] using hnonzero

end

end DedekindZeta
