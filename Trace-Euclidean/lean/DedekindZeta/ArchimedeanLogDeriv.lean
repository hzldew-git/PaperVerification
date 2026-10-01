/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Logarithmic derivative of the archimedean Dedekind-zeta factor

This module expands the logarithmic derivative of `ZInfty` into its
discriminant and digamma terms.  It is the archimedean input needed before the
Stark--Weil contour identity can be specialized to the Odlyzko test kernel.
-/

open NumberField NumberField.InfinitePlace Complex

namespace DedekindZeta.ArchimedeanLogDeriv

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

private theorem discrBase_ne_zero :
    (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := by
  exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))

private theorem logDeriv_const_cpow_linear
    (c a s : ℂ) (hc : c ≠ 0) :
    logDeriv (fun z : ℂ => c ^ (a * z)) s = Complex.log c * a := by
  have h := ((hasDerivAt_id s).const_mul a).const_cpow (c := c) (Or.inl hc)
  have hderiv : deriv (fun z : ℂ => c ^ (a * z)) s =
      c ^ (a * s) * Complex.log c * a := by
    simpa only [id_eq, mul_one] using h.deriv
  rw [logDeriv_apply, hderiv]
  have hpow : c ^ (a * s) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp [hpow]

private theorem logDeriv_const_cpow_half
    (c s : ℂ) (hc : c ≠ 0) :
    logDeriv (fun z : ℂ => c ^ (z / 2)) s = Complex.log c / 2 := by
  have h := logDeriv_const_cpow_linear c (1 / 2) s hc
  convert h using 1 <;> ring_nf

private theorem logDeriv_const_cpow_neg_half
    (c s : ℂ) (hc : c ≠ 0) :
    logDeriv (fun z : ℂ => c ^ (-z / 2)) s = -Complex.log c / 2 := by
  have h := logDeriv_const_cpow_linear c (-1 / 2) s hc
  convert h using 1 <;> ring_nf

private theorem logDeriv_const_cpow_neg
    (c s : ℂ) (hc : c ≠ 0) :
    logDeriv (fun z : ℂ => c ^ (-z)) s = -Complex.log c := by
  have h := logDeriv_const_cpow_linear c (-1) s hc
  convert h using 1 <;> ring_nf

private theorem gamma_half_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  have harg : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num [Complex.div_re] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact (Complex.differentiableAt_Gamma (s / 2) harg).comp s
    (differentiableAt_id.div_const 2)

private theorem gamma_half_ne_zero {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma (s / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  norm_num [Complex.div_re]
  linarith

/-- Logarithmic derivative of `Gamma(s / 2)` in the positive half-plane. -/
theorem logDeriv_Gamma_half {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      Complex.digamma (s / 2) / 2 := by
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by
    simpa only [id_eq] using
      (differentiableAt_id.div_const (2 : ℂ))
  have h := logDeriv_comp
    (f := Complex.Gamma)
    (g := fun z : ℂ => z / 2)
    (x := s)
    (Complex.differentiableAt_Gamma (s / 2) (by
      intro m heq
      have hre := congrArg Complex.re heq
      norm_num [Complex.div_re] at hre
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith))
    hdiv
  change logDeriv (Complex.Gamma ∘ fun z : ℂ => z / 2) s = _
  rw [h, ← Complex.digamma_def]
  simp [div_eq_mul_inv]

/-- Logarithmic derivative of the real archimedean Gamma factor. -/
theorem logDeriv_LReal {s : ℂ} (hs : 0 < s.re) :
    logDeriv (LReal : ℂ → ℂ) s =
      -Complex.log (Real.pi : ℂ) / 2 +
        Complex.digamma (s / 2) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hGamma_ne := gamma_half_ne_zero hs
  have hpow_diff : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hπ)
  have hGamma_diff := gamma_half_differentiableAt hs
  unfold LReal
  rw [logDeriv_mul s hpow_ne hGamma_ne hpow_diff hGamma_diff,
    logDeriv_const_cpow_neg_half (Real.pi : ℂ) s hπ,
    logDeriv_Gamma_half hs]

/-- Logarithmic derivative of the complex archimedean Gamma factor. -/
theorem logDeriv_LComplex {s : ℂ} (hs : 0 < s.re) :
    logDeriv (LComplex : ℂ → ℂ) s =
      -Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s := by
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow_ne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hGamma_ne : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs
  have hpow_diff : DifferentiableAt ℂ
      (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hbase)
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (by
      intro m heq
      have hre := congrArg Complex.re heq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have hleft_ne :
      2 * (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    mul_ne_zero (by norm_num) hpow_ne
  have hleft_diff : DifferentiableAt ℂ
      (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    (differentiableAt_const (2 : ℂ)).mul hpow_diff
  unfold LComplex
  rw [logDeriv_mul s hleft_ne hGamma_ne hleft_diff hGamma_diff,
    logDeriv_const_mul s (2 : ℂ) (by norm_num),
    logDeriv_const_cpow_neg (2 * (Real.pi : ℂ)) s hbase,
    ← Complex.digamma_def]

/-- Full archimedean logarithmic derivative of the completed Dedekind zeta
factor on the positive half-plane. -/
theorem logDeriv_ZInfty {s : ℂ} (hs : 0 < s.re) :
    logDeriv (ZInfty K) s =
      Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) / 2 +
        (nrRealPlaces K : ℂ) *
          (-Complex.log (Real.pi : ℂ) / 2 +
            Complex.digamma (s / 2) / 2) +
        (nrComplexPlaces K : ℂ) *
          (-Complex.log (2 * (Real.pi : ℂ)) + Complex.digamma s) := by
  have hD : (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := discrBase_ne_zero K
  have hDpow_ne : (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl hD)
  have hDpow_diff : DifferentiableAt ℂ
      (fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2))) s :=
    (differentiableAt_id.div_const 2).const_cpow (Or.inl hD)
  have hReal_ne : LReal s ≠ 0 := by
    unfold LReal
    exact mul_ne_zero
      (cpow_ne_zero_iff.mpr (Or.inl
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (gamma_half_ne_zero hs)
  have hComplex_ne : LComplex s ≠ 0 := by
    unfold LComplex
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
      (Complex.Gamma_ne_zero_of_re_pos hs)
  have hReal_diff : DifferentiableAt ℂ LReal s := by
    unfold LReal
    exact (((differentiableAt_id.neg).div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        (gamma_half_differentiableAt hs)
  have hComplex_diff : DifferentiableAt ℂ LComplex s := by
    unfold LComplex
    exact ((differentiableAt_const (2 : ℂ)).mul
      (differentiableAt_id.neg.const_cpow (Or.inl (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))).mul
          (Complex.differentiableAt_Gamma s (by
            intro m heq
            have hre := congrArg Complex.re heq
            simp only [Complex.neg_re, Complex.natCast_re] at hre
            have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith))
  have hleft_ne :
      (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
        LReal s ^ nrRealPlaces K ≠ 0 :=
    mul_ne_zero hDpow_ne (pow_ne_zero _ hReal_ne)
  have hRealPow_ne : LReal s ^ nrRealPlaces K ≠ 0 :=
    pow_ne_zero _ hReal_ne
  have hComplexPow_ne : LComplex s ^ nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ hComplex_ne
  have hleft_diff : DifferentiableAt ℂ
      (fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2)) *
        LReal z ^ nrRealPlaces K) s :=
    hDpow_diff.mul (hReal_diff.pow _)
  unfold ZInfty
  rw [logDeriv_mul
      (f := fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2)) *
        LReal z ^ nrRealPlaces K)
      (g := fun z : ℂ => LComplex z ^ nrComplexPlaces K)
      s hleft_ne hComplexPow_ne hleft_diff (hComplex_diff.pow _),
    logDeriv_mul
      (f := fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2)))
      (g := fun z : ℂ => LReal z ^ nrRealPlaces K)
      s hDpow_ne hRealPow_ne hDpow_diff (hReal_diff.pow _),
    logDeriv_const_cpow_half _ s hD,
    logDeriv_fun_pow hReal_diff, logDeriv_fun_pow hComplex_diff,
    logDeriv_LReal hs, logDeriv_LComplex hs]

end

end DedekindZeta.ArchimedeanLogDeriv
