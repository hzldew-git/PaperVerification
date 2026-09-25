/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.ArchimedeanLogDeriv
import DedekindZeta.DigammaSeries
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Digamma identities for the Dedekind-zeta archimedean line

This module records the conjugation and duplication identities needed to
reorganize the real and complex infinite-place factors in the explicit
formula.
-/

open Complex

namespace DedekindZeta.DigammaIdentities

noncomputable section

/-- The digamma function commutes with complex conjugation. -/
theorem digamma_conj (z : ℂ) :
    Complex.digamma (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.digamma z) := by
  have hGamma :
      (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) =
        Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hderiv : deriv Complex.Gamma (starRingEnd ℂ z) =
      starRingEnd ℂ (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hGamma, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hderiv, Complex.Gamma_conj, ← map_div₀]

/-- Legendre's duplication formula after taking logarithmic derivatives. -/
theorem digamma_duplication {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z + Complex.digamma (z + 1 / 2) =
      2 * Complex.digamma (2 * z) - 2 * Complex.log 2 := by
  have gammaDiffOfPos : ∀ {w : ℂ}, 0 < w.re →
      DifferentiableAt ℂ Complex.Gamma w := by
    intro w hw
    exact Complex.differentiableAt_Gamma w (by
      intro m h
      have hre := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have hzGammaDiff : DifferentiableAt ℂ Complex.Gamma z :=
    gammaDiffOfPos hz
  have hzGammaNe : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hz
  have hplusPos : 0 < (z + 1 / 2).re := by
    norm_num
    linarith
  have hplusDiff : DifferentiableAt ℂ Complex.Gamma (z + 1 / 2) :=
    gammaDiffOfPos hplusPos
  have hplusNe : Complex.Gamma (z + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hplusPos
  have hdoublePos : 0 < (2 * z).re := by
    norm_num
    linarith
  have hdoubleDiff : DifferentiableAt ℂ Complex.Gamma (2 * z) :=
    gammaDiffOfPos hdoublePos
  have hdoubleNe : Complex.Gamma (2 * z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdoublePos
  have haddDiff : DifferentiableAt ℂ (fun w : ℂ => w + 1 / 2) z := by
    fun_prop
  have hmulDiff : DifferentiableAt ℂ (fun w : ℂ => 2 * w) z := by
    fun_prop
  have hlogAdd :
      logDeriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z =
        Complex.digamma (z + 1 / 2) := by
    have h := logDeriv_comp
      (f := Complex.Gamma) (g := fun w : ℂ => w + 1 / 2) (x := z)
      hplusDiff haddDiff
    rw [← Complex.digamma_def] at h
    change logDeriv (Complex.Gamma ∘ fun w : ℂ => w + 1 / 2) z = _
    simpa using h
  have hlogDouble :
      logDeriv (fun w : ℂ => Complex.Gamma (2 * w)) z =
        2 * Complex.digamma (2 * z) := by
    have h := logDeriv_comp
      (f := Complex.Gamma) (g := fun w : ℂ => 2 * w) (x := z)
      hdoubleDiff hmulDiff
    rw [← Complex.digamma_def] at h
    have hderiv : deriv (fun w : ℂ => 2 * w) z = 2 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id z).const_mul (2 : ℂ)).deriv
    rw [hderiv] at h
    change logDeriv (Complex.Gamma ∘ fun w : ℂ => 2 * w) z = _
    simpa [mul_comm] using h
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpowNe : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl htwo)
  have hpowDeriv : HasDerivAt
      (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
      ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2)) z := by
    have h := ((hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).const_mul 2)).const_cpow (Or.inl htwo)
    simpa only [Pi.sub_apply, Pi.one_apply, id_eq, zero_sub, mul_one] using h
  have hlogPow :
      logDeriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z =
        -2 * Complex.log 2 := by
    rw [logDeriv_apply, hpowDeriv.deriv]
    field_simp [hpowNe]
  have hroot : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hleft := logDeriv_mul
    (f := Complex.Gamma)
    (g := fun w : ℂ => Complex.Gamma (w + 1 / 2))
    z hzGammaNe hplusNe hzGammaDiff
      (hplusDiff.comp z haddDiff)
  have hrightInner := logDeriv_mul
    (f := fun w : ℂ => Complex.Gamma (2 * w))
    (g := fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
    z hdoubleNe hpowNe (hdoubleDiff.comp z hmulDiff)
      hpowDeriv.differentiableAt
  have hright := logDeriv_mul_const
    (f := fun w : ℂ => Complex.Gamma (2 * w) *
      (2 : ℂ) ^ (1 - 2 * w)) z
    ((Real.sqrt Real.pi : ℝ) : ℂ) hroot
  have hfun :
      (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =
        (fun w : ℂ =>
          (Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w)) *
            ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
    funext w
    exact Complex.Gamma_mul_Gamma_add_half w
  have heq := congrArg (fun f : ℂ → ℂ => logDeriv f z) hfun
  rw [hleft, hlogAdd, ← Complex.digamma_def,
    hright, hrightInner, hlogDouble, hlogPow] at heq
  simpa [sub_eq_add_neg] using heq

/-- The symmetric critical-line bracket for the full number-field
archimedean factor. -/
theorem logDeriv_ZInfty_critical_bracket
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    logDeriv (ZInfty K) ((1 / 2 : ℂ) + (t : ℂ) * I) +
        logDeriv (ZInfty K) ((1 / 2 : ℂ) - (t : ℂ) * I) =
      Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) +
        (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
          (-Complex.log (Real.pi : ℂ) +
            ((Complex.digamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re : ℂ)) +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-2 * Complex.log (2 * (Real.pi : ℂ)) +
            2 * ((Complex.digamma ((1 / 2 : ℂ) + (t : ℂ) * I)).re : ℂ)) := by
  let sp : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  let sm : ℂ := (1 / 2 : ℂ) - (t : ℂ) * I
  let wReal : ℂ := (1 / 4 : ℂ) + (t / 2 : ℝ) * I
  let wComplex : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hsp : 0 < sp.re := by
    dsimp [sp]
    norm_num
  have hsm : 0 < sm.re := by
    dsimp [sm]
    norm_num
  have hspHalf : sp / 2 = wReal := by
    dsimp [sp, wReal]
    push_cast
    ring
  have hsmHalf : sm / 2 = starRingEnd ℂ wReal := by
    have hw : starRingEnd ℂ wReal =
        (1 / 4 : ℂ) - ((t / 2 : ℝ) : ℂ) * I := by
      dsimp [wReal]
      simp only [map_add, map_mul, map_div₀, map_one, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [hw]
    dsimp [sm]
    push_cast
    ring
  have hspEq : sp = wComplex := by rfl
  have hsmEq : sm = starRingEnd ℂ wComplex := by
    dsimp [sm, wComplex]
    apply Complex.ext <;> simp
  have hRealConj :
      Complex.digamma (sm / 2) =
        starRingEnd ℂ (Complex.digamma wReal) := by
    rw [hsmHalf, digamma_conj]
  have hComplexConj :
      Complex.digamma sm =
        starRingEnd ℂ (Complex.digamma wComplex) := by
    rw [hsmEq, digamma_conj]
  have hRealSum :
      Complex.digamma wReal + starRingEnd ℂ (Complex.digamma wReal) =
        2 * ((Complex.digamma wReal).re : ℂ) := by
    rw [Complex.add_conj]
    push_cast
    rfl
  have hComplexSum :
      Complex.digamma wComplex + starRingEnd ℂ (Complex.digamma wComplex) =
        2 * ((Complex.digamma wComplex).re : ℂ) := by
    rw [Complex.add_conj]
    push_cast
    rfl
  change logDeriv (ZInfty K) sp + logDeriv (ZInfty K) sm = _
  rw [ArchimedeanLogDeriv.logDeriv_ZInfty K hsp,
    ArchimedeanLogDeriv.logDeriv_ZInfty K hsm,
    hspHalf, hspEq, hRealConj, hComplexConj]
  dsimp only [wReal, wComplex] at hRealSum hComplexSum ⊢
  linear_combination
    (NumberField.InfinitePlace.nrRealPlaces K : ℂ) / 2 * hRealSum +
      (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * hComplexSum

end

end DedekindZeta.DigammaIdentities
