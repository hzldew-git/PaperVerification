/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.IdealEulerProduct
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-ideal Euler factors and logarithmic derivatives

This module supplies the locally uniform Euler-product interface needed for
the prime side of the Dedekind-zeta explicit formula.  We first work with the
non-inverted factors `1 - N(P)^{-s}`.  Their locally uniform product is easier
to control, and its product is the reciprocal of `dedekindZeta` on `re s > 1`.
-/

open NumberField IsDedekindDomain Filter Set Topology Complex
open scoped Real nonZeroDivisors Topology

namespace DedekindZeta

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- The Euler parameter `N(P)^{-s}` attached to a nonzero prime ideal. -/
def primeEulerParameter (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

/-- The non-inverted local Euler factor. -/
def primeEulerBaseFactor (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  1 - primeEulerParameter K v s

/-- The product of the non-inverted local Euler factors. -/
def primeEulerBaseProduct (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 K), primeEulerBaseFactor K v s

/-- The logarithm-weighted prime-power term attached to `P` and the positive
exponent `m + 1`. -/
def primePowerLogTerm (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (s : ℂ) : ℂ :=
  Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
    (primeEulerParameter K v s) ^ (m + 1)

private theorem primeIdeal_absNorm_one_lt
    (v : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm v.asIdeal := by
  have hNneZero : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h)
  have hNneOne : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h
    exact v.isPrime.ne_top ((Ideal.absNorm_eq_one_iff).mp h)
  omega

/-- The norm of a prime Euler parameter is the corresponding real power. -/
theorem norm_primeEulerParameter (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖primeEulerParameter K v s‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  have hNpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
  rw [primeEulerParameter, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]

/-- The derivative of the Euler parameter `N(P)^{-s}`. -/
theorem hasDerivAt_primeEulerParameter
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    HasDerivAt (primeEulerParameter K v)
      (-Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
        primeEulerParameter K v s) s := by
  have hNneZero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)).ne'
  have h := (hasDerivAt_neg' s).const_cpow
    (c := (Ideal.absNorm v.asIdeal : ℂ)) (Or.inl hNneZero)
  convert h using 1 <;> try rfl
  rw [primeEulerParameter]
  ring

/-- The derivative of a non-inverted prime Euler factor. -/
theorem hasDerivAt_primeEulerBaseFactor
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    HasDerivAt (primeEulerBaseFactor K v)
      (Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
        primeEulerParameter K v s) s := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (hasDerivAt_primeEulerParameter K v s)
  convert h using 1 <;> try rfl
  ring

/-- The logarithmic derivative of one non-inverted prime Euler factor. -/
theorem logDeriv_primeEulerBaseFactor
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    logDeriv (primeEulerBaseFactor K v) s =
      Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
        primeEulerParameter K v s / primeEulerBaseFactor K v s := by
  rw [logDeriv_apply, (hasDerivAt_primeEulerBaseFactor K v s).deriv]

/-- The geometric-series expansion of one non-inverted Euler factor. -/
theorem primeEulerParameter_div_baseFactor_eq_tsum
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    primeEulerParameter K v s / primeEulerBaseFactor K v s =
      ∑' m : ℕ, (primeEulerParameter K v s) ^ (m + 1) := by
  have hlt : ‖primeEulerParameter K v s‖ < 1 := by
    simpa only [primeEulerParameter] using
      norm_primeIdeal_absNorm_neg_cpow_lt_one K hs v
  rw [primeEulerBaseFactor, div_eq_mul_inv,
    ← tsum_geometric_of_norm_lt_one hlt]
  exact geom_series_mul_shift (primeEulerParameter K v s) hlt

/-- One local logarithmic derivative is the absolutely convergent sum over
the positive powers of the corresponding prime ideal. -/
theorem logDeriv_primeEulerBaseFactor_eq_tsum_primePowers
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (primeEulerBaseFactor K v) s =
      ∑' m : ℕ, primePowerLogTerm K v m s := by
  rw [logDeriv_primeEulerBaseFactor K v s, mul_div_assoc,
    primeEulerParameter_div_baseFactor_eq_tsum K v hs, ← tsum_mul_left]
  rfl

/-- Norm of a logarithm-weighted prime-power term. -/
theorem norm_primePowerLogTerm
    (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (s : ℂ) :
    ‖primePowerLogTerm K v m s‖ =
      Real.log (Ideal.absNorm v.asIdeal : ℝ) *
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ (m + 1) := by
  rw [primePowerLogTerm, norm_mul, norm_pow, norm_primeEulerParameter K]
  rw [← Complex.natCast_log, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg _)]

/-- The norms of the logarithm-weighted double series over prime ideals and
their positive powers are summable on `re s > 1`. -/
theorem summable_norm_primePowerLogTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      ‖primePowerLogTerm K p.1 p.2 s‖) := by
  let ε : ℝ := (s.re - 1) / 2
  let τ : ℝ := (s.re + 1) / 2
  let c : ℝ := (2 : ℝ) ^ (-s.re)
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hτ : 1 < τ := by
    dsimp [τ]
    linarith
  have hc : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsumτ : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ)) := by
    have hsum := summable_primeIdeal_absNorm_neg_cpow K
      (s := (τ : ℂ)) (by simpa using hτ)
    refine hsum.congr (fun v => ?_)
    have hNpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
    rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    rfl
  have hinner : ∀ v : HeightOneSpectrum (𝓞 K),
      Summable (fun m : ℕ => ‖primePowerLogTerm K v m s‖) := by
    intro v
    let q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)
    have hNpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
    have hq0 : 0 ≤ q := Real.rpow_nonneg hNpos.le _
    have hq1 : q < 1 := by
      dsimp [q]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast primeIdeal_absNorm_one_lt K v) (by linarith)
    have hgeom : Summable (fun m : ℕ => q ^ m) :=
      summable_geometric_of_lt_one hq0 hq1
    refine (hgeom.mul_left
      (Real.log (Ideal.absNorm v.asIdeal : ℝ) * q)).congr (fun m => ?_)
    rw [norm_primePowerLogTerm K]
    dsimp [q]
    rw [pow_succ']
    ring
  have hinner_tsum (v : HeightOneSpectrum (𝓞 K)) :
      (∑' m : ℕ, ‖primePowerLogTerm K v m s‖) =
        Real.log (Ideal.absNorm v.asIdeal : ℝ) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) *
            (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))⁻¹ := by
    let q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)
    have hNpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
    have hq0 : 0 ≤ q := Real.rpow_nonneg hNpos.le _
    have hq1 : q < 1 := by
      dsimp [q]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast primeIdeal_absNorm_one_lt K v) (by linarith)
    calc
      (∑' m : ℕ, ‖primePowerLogTerm K v m s‖) =
          ∑' m : ℕ,
            (Real.log (Ideal.absNorm v.asIdeal : ℝ) * q) * q ^ m := by
              apply tsum_congr
              intro m
              rw [norm_primePowerLogTerm K]
              dsimp [q]
              rw [pow_succ']
              ring
      _ = (Real.log (Ideal.absNorm v.asIdeal : ℝ) * q) *
          ∑' m : ℕ, q ^ m := by rw [tsum_mul_left]
      _ = Real.log (Ideal.absNorm v.asIdeal : ℝ) * q * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
      _ = Real.log (Ideal.absNorm v.asIdeal : ℝ) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) *
            (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))⁻¹ := by rfl
  have houter : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ∑' m : ℕ, ‖primePowerLogTerm K v m s‖) := by
    refine (hsumτ.mul_left (ε⁻¹ * (1 - c)⁻¹)).of_nonneg_of_le
      (fun v => tsum_nonneg (fun _ => norm_nonneg _)) (fun v => ?_)
    have hNtwo : 2 ≤ Ideal.absNorm v.asIdeal :=
      primeIdeal_absNorm_one_lt K v
    have hNpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hNtwo)
    have hlog : Real.log (Ideal.absNorm v.asIdeal : ℝ) ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ ε / ε :=
      Real.log_natCast_le_rpow_div (Ideal.absNorm v.asIdeal) hε
    have hq0 : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg hNpos.le _
    have hq1 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast primeIdeal_absNorm_one_lt K v) (by linarith)
    have hq_le : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ c := by
      dsimp [c]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by exact_mod_cast hNtwo) (by linarith)
    have hinv :
        (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))⁻¹ ≤
          (1 - c)⁻¹ :=
      (inv_le_inv₀ (sub_pos.mpr hq1) (sub_pos.mpr hc)).2
        (sub_le_sub_left hq_le 1)
    have hrpow :
        (Ideal.absNorm v.asIdeal : ℝ) ^ ε *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) =
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      dsimp [ε, τ]
      ring
    rw [hinner_tsum v]
    calc
      Real.log (Ideal.absNorm v.asIdeal : ℝ) *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) *
              (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))⁻¹
          ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ ε / ε) *
              (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) * (1 - c)⁻¹ := by
                gcongr
      _ = (ε⁻¹ * (1 - c)⁻¹) *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ) := by
              rw [div_eq_mul_inv, ← hrpow]
              ring
  have hnorm : Summable
      (fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
        ‖primePowerLogTerm K p.1 p.2 s‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨hinner, houter⟩
  exact hnorm

/-- The logarithm-weighted double series over prime ideals and their positive
powers is absolutely summable on `re s > 1`. -/
theorem summable_primePowerLogTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      primePowerLogTerm K p.1 p.2 s) :=
  (summable_norm_primePowerLogTerm K hs).of_norm

/-- Fubini identity for the absolutely convergent prime-power logarithmic
series. -/
theorem tsum_primePowerLogTerm_prod {s : ℂ} (hs : 1 < s.re) :
    (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
      primePowerLogTerm K p.1 p.2 s) =
      ∑' v : HeightOneSpectrum (𝓞 K),
        ∑' m : ℕ, primePowerLogTerm K v m s := by
  simpa using (summable_primePowerLogTerm K hs).tsum_prod

/-- The logarithmic derivatives of the non-inverted prime Euler factors are
absolutely summable on `re s > 1`. -/
theorem summable_logDeriv_primeEulerBaseFactor {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      logDeriv (primeEulerBaseFactor K v) s) := by
  let ε : ℝ := (s.re - 1) / 2
  let τ : ℝ := (s.re + 1) / 2
  let c : ℝ := (2 : ℝ) ^ (-s.re)
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hτ : 1 < τ := by
    dsimp [τ]
    linarith
  have hc : c < 1 := by
    dsimp [c]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsumτ : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ)) := by
    have hsum := summable_primeIdeal_absNorm_neg_cpow K
      (s := (τ : ℂ)) (by simpa using hτ)
    refine hsum.congr (fun v => ?_)
    have hNpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
    rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    rfl
  refine Summable.of_norm_bounded
    (hsumτ.mul_left (ε⁻¹ * (1 - c)⁻¹)) (fun v => ?_)
  have hNtwo : 2 ≤ Ideal.absNorm v.asIdeal :=
    primeIdeal_absNorm_one_lt K v
  have hNpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hNtwo)
  have hlog : ‖Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ ε / ε := by
    simpa using
      (Complex.norm_log_natCast_le_rpow_div (Ideal.absNorm v.asIdeal) hε)
  have hparameter : ‖primeEulerParameter K v s‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
    norm_primeEulerParameter K v s
  have hparameter_le : ‖primeEulerParameter K v s‖ ≤ c := by
    rw [hparameter]
    dsimp [c]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast hNtwo) (by linarith)
  have hfactor_ne : primeEulerBaseFactor K v s ≠ 0 := by
    intro hzero
    have hone : primeEulerParameter K v s = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hnorm := congrArg norm hone
    rw [norm_one] at hnorm
    have hlt : ‖primeEulerParameter K v s‖ < 1 :=
      hparameter_le.trans_lt hc
    linarith
  have hfactor_pos : 0 < ‖primeEulerBaseFactor K v s‖ :=
    norm_pos_iff.mpr hfactor_ne
  have hfactor_lower : 1 - c ≤ ‖primeEulerBaseFactor K v s‖ := by
    calc
      1 - c ≤ 1 - ‖primeEulerParameter K v s‖ :=
        sub_le_sub_left hparameter_le 1
      _ ≤ ‖(1 : ℂ) - primeEulerParameter K v s‖ := by
        simpa only [norm_one] using
          (norm_sub_norm_le (1 : ℂ) (primeEulerParameter K v s))
      _ = ‖primeEulerBaseFactor K v s‖ := rfl
  have hinv : ‖(primeEulerBaseFactor K v s)⁻¹‖ ≤ (1 - c)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hfactor_pos (sub_pos.mpr hc)).2 hfactor_lower
  have hrpow :
      (Ideal.absNorm v.asIdeal : ℝ) ^ ε *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    dsimp [ε, τ]
    ring
  rw [logDeriv_primeEulerBaseFactor K v s, div_eq_mul_inv,
    norm_mul, norm_mul, hparameter]
  calc
    (‖Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) *
        ‖(primeEulerBaseFactor K v s)⁻¹‖
        ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ ε / ε) *
            (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) * (1 - c)⁻¹ := by
              gcongr
    _ = (ε⁻¹ * (1 - c)⁻¹) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-τ) := by
            rw [div_eq_mul_inv, ← hrpow]
            ring

/-- The non-inverted prime Euler factors form a locally uniformly convergent
product on every closed-away-from-one right half-plane. -/
theorem multipliableLocallyUniformlyOn_primeEulerBaseFactor
    {σ : ℝ} (hσ : 1 < σ) :
    MultipliableLocallyUniformlyOn
      (fun v : HeightOneSpectrum (𝓞 K) => primeEulerBaseFactor K v)
      {s : ℂ | σ < s.re} := by
  let u : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
  have hsumu : Summable u := by
    have hsum := summable_primeIdeal_absNorm_neg_cpow K
      (s := (σ : ℂ)) (by simpa using hσ)
    refine hsum.congr (fun v => ?_)
    dsimp only [u]
    have hNpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)
    rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    rfl
  have hbound : ∀ v, ∀ s ∈ {z : ℂ | σ < z.re},
      ‖-primeEulerParameter K v s‖ ≤ u v := by
    intro v s hs
    rw [norm_neg, norm_primeEulerParameter K]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (primeIdeal_absNorm_one_lt K v).le)
      (neg_le_neg hs.le)
  have hcts : ∀ v, ContinuousOn
      (fun s : ℂ => -primeEulerParameter K v s) {s : ℂ | σ < s.re} := by
    intro v
    have hNneZero : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.zero_lt_of_lt (primeIdeal_absNorm_one_lt K v)).ne'
    have hdiff : Differentiable ℂ (primeEulerParameter K v) := by
      exact differentiable_neg.const_cpow (Or.inl hNneZero)
    exact hdiff.continuous.neg.continuousOn
  have hopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h := Summable.multipliableLocallyUniformlyOn_one_add
    (f := fun v s => -primeEulerParameter K v s) hopen hsumu
    (Filter.Eventually.of_forall hbound) hcts
  rcases h with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  simpa only [primeEulerBaseFactor, sub_eq_add_neg,
    HasProdLocallyUniformlyOn] using hF

/-- Every non-inverted prime Euler factor is nonzero on `re s > 1`. -/
theorem primeEulerBaseFactor_ne_zero {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) :
    primeEulerBaseFactor K v s ≠ 0 := by
  intro hzero
  have hone : primeEulerParameter K v s = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  have hlt := norm_primeIdeal_absNorm_neg_cpow_lt_one K hs v
  have hlt' : ‖primeEulerParameter K v s‖ < 1 := by
    simpa only [primeEulerParameter] using hlt
  linarith

/-- The product of the non-inverted prime Euler factors is nonzero on the
half-plane of absolute convergence. -/
theorem primeEulerBaseProduct_ne_zero {s : ℂ} (hs : 1 < s.re) :
    primeEulerBaseProduct K s ≠ 0 := by
  have hsum : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ‖-primeEulerParameter K v s‖) := by
    simpa only [norm_neg, primeEulerParameter] using
      summable_primeIdeal_absNorm_neg_cpow K hs
  have hprod := tprod_one_add_ne_zero_of_summable
    (f := fun v : HeightOneSpectrum (𝓞 K) => -primeEulerParameter K v s)
    (fun v => by
      simpa only [primeEulerBaseFactor, sub_eq_add_neg] using
        primeEulerBaseFactor_ne_zero K hs v)
    hsum
  simpa only [primeEulerBaseProduct, primeEulerBaseFactor, sub_eq_add_neg] using hprod

/-- On `re s > 1`, the non-inverted prime Euler product is the reciprocal of
the Dedekind zeta function. -/
theorem primeEulerBaseProduct_mul_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    primeEulerBaseProduct K s * NumberField.dedekindZeta K s = 1 := by
  have hsum : Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ‖-primeEulerParameter K v s‖) := by
    simpa only [norm_neg, primeEulerParameter] using
      summable_primeIdeal_absNorm_neg_cpow K hs
  have hbase : Multipliable
      (fun v : HeightOneSpectrum (𝓞 K) => primeEulerBaseFactor K v s) := by
    simpa only [primeEulerBaseFactor, sub_eq_add_neg] using
      multipliable_one_add_of_summable hsum
  have hEuler := hasProd_primeIdeal_eulerFactors K hs
  have hmul := hbase.hasProd.mul hEuler
  have hone : HasProd (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ))
      (primeEulerBaseProduct K s * NumberField.dedekindZeta K s) := by
    apply hmul.congr_fun
    intro v
    exact (mul_inv_cancel₀ (primeEulerBaseFactor_ne_zero K hs v)).symm
  exact hone.unique hasProd_one

/-- The logarithmic derivative of the non-inverted Euler product is the
absolutely convergent sum of the local logarithmic derivatives. -/
theorem logDeriv_primeEulerBaseProduct_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    logDeriv (primeEulerBaseProduct K) s =
      ∑' v : HeightOneSpectrum (𝓞 K),
        logDeriv (primeEulerBaseFactor K v) s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by
    dsimp [σ]
    linarith
  have hsσ : s ∈ {z : ℂ | σ < z.re} := by
    dsimp [σ]
    linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have htend := multipliableLocallyUniformlyOn_primeEulerBaseFactor K hσ
  have hprod : HasProdLocallyUniformlyOn
      (fun v : HeightOneSpectrum (𝓞 K) => primeEulerBaseFactor K v)
      (primeEulerBaseProduct K) {z : ℂ | σ < z.re} := by
    change HasProdLocallyUniformlyOn
      (fun v : HeightOneSpectrum (𝓞 K) => primeEulerBaseFactor K v)
      (fun z => ∏' v : HeightOneSpectrum (𝓞 K), primeEulerBaseFactor K v z)
      {z : ℂ | σ < z.re}
    exact htend.hasProdLocallyUniformlyOn
  have hsum := summable_logDeriv_primeEulerBaseFactor K hs
  rw [Eq.comm, ← hsum.hasSum_iff]
  refine (logDeriv_tendsto hopen hsσ hprod
    (.of_forall <| fun b => DifferentiableOn.fun_finsetProd fun v _ z _ =>
      (hasDerivAt_primeEulerBaseFactor K v z).differentiableAt.differentiableWithinAt)
    (primeEulerBaseProduct_ne_zero K hs)).congr fun b => ?_
  rw [logDeriv_prod
    (fun v _ => primeEulerBaseFactor_ne_zero K hs v)
    (fun v _ => (hasDerivAt_primeEulerBaseFactor K v s).differentiableAt)]

end

end DedekindZeta
