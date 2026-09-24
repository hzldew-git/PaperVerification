import DedekindZeta.GlobalContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Removing the archimedean factor

The entire completed zeta constructed from the number-field theta integral
still contains Gamma factors. We use the shifted real Gamma factor to remove
the apparent singularity at `s = 0` in its reciprocal normalization.
-/

open NumberField NumberField.InfinitePlace Complex

namespace DedekindZeta.ZetaRegularization

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

private theorem archimedeanCount_pos :
    0 < nrRealPlaces K + nrComplexPlaces K := by
  rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Fintype.card_pos

private theorem discrBase_ne_zero :
    (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := by
  exact_mod_cast (abs_ne_zero.mpr (NumberField.discr_ne_zero K))

/-- The reciprocal of `s * ZInfty(s)`, written as an entire expression.
One real Gamma factor is absorbed using `Gammaℝ(s+2) = s Gammaℝ(s)/(2π)`. -/
def inverseCompletedMultiplier (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (-(s / 2))) *
    ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹) *
      ((Gammaℝ s)⁻¹) ^ (nrRealPlaces K + nrComplexPlaces K - 1) *
        ((Gammaℝ (s + 1))⁻¹) ^ nrComplexPlaces K

theorem inverseCompletedMultiplier_analyticOn :
    AnalyticOnNhd ℂ (inverseCompletedMultiplier K) Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  have hD : DifferentiableAt ℂ
      (fun z : ℂ => (((|NumberField.discr K| : ℤ) : ℂ) ^ (-(z / 2)))) s :=
    ((differentiableAt_id.div_const 2).neg).const_cpow
      (Or.inl (discrBase_ne_zero K))
  have hG : DifferentiableAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.differentiableAt
  have hG2 : DifferentiableAt ℂ (fun z : ℂ => (Gammaℝ (z + 2))⁻¹) s :=
    differentiable_Gammaℝ_inv.differentiableAt.comp s
      (differentiableAt_id.add_const 2)
  have hG1 : DifferentiableAt ℂ (fun z : ℂ => (Gammaℝ (z + 1))⁻¹) s :=
    differentiable_Gammaℝ_inv.differentiableAt.comp s
      (differentiableAt_id.add_const 1)
  unfold inverseCompletedMultiplier
  exact ((hD.mul ((differentiableAt_const _).mul hG2)).mul
    (hG.pow _)).mul (hG1.pow _)

private theorem ZInfty_eq_GammaR (s : ℂ) :
    ZInfty K s =
      (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
        (Gammaℝ s) ^ (nrRealPlaces K + nrComplexPlaces K) *
          (Gammaℝ (s + 1)) ^ nrComplexPlaces K := by
  change (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
      (Gammaℝ s) ^ nrRealPlaces K * (Gammaℂ s) ^ nrComplexPlaces K = _
  rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_pow, pow_add]
  ring

private theorem shiftedGamma_cancel {s : ℂ} (hs₀ : s ≠ 0)
    (hG : Gammaℝ s ≠ 0) :
    ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹) *
      (s * Gammaℝ s) = 1 := by
  rw [Gammaℝ_add_two hs₀]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hs₀, hG, hp]

/-- On the original half-plane, the entire multiplier exactly inverts
`s * ZInfty(s)`. -/
theorem inverseCompletedMultiplier_mul {s : ℂ} (hs : 1 < s.re) :
    inverseCompletedMultiplier K s * (s * ZInfty K s) = 1 := by
  have hs₀ : s ≠ 0 := by
    intro heq
    subst s
    norm_num at hs
  have hG : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hG1 : Gammaℝ (s + 1) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hDpow : (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (discrBase_ne_zero K))
  have hn : nrRealPlaces K + nrComplexPlaces K - 1 + 1 =
      nrRealPlaces K + nrComplexPlaces K := by
    have hpos := archimedeanCount_pos K
    omega
  have hshift := shiftedGamma_cancel hs₀ hG
  rw [ZInfty_eq_GammaR, ← hn, pow_add, pow_one]
  unfold inverseCompletedMultiplier
  rw [cpow_neg]
  have hDcancel : (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ *
      (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) = 1 :=
    inv_mul_cancel₀ hDpow
  have hGcancel : ((Gammaℝ s)⁻¹) ^ (nrRealPlaces K + nrComplexPlaces K - 1) *
      (Gammaℝ s) ^ (nrRealPlaces K + nrComplexPlaces K - 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hG, one_pow]
  have hG1cancel : ((Gammaℝ (s + 1))⁻¹) ^ nrComplexPlaces K *
      (Gammaℝ (s + 1)) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hG1, one_pow]
  calc
    _ = ( (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) ) *
        ( ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹) *
          (s * Gammaℝ s) ) *
        ( ((Gammaℝ s)⁻¹) ^ (nrRealPlaces K + nrComplexPlaces K - 1) *
          (Gammaℝ s) ^ (nrRealPlaces K + nrComplexPlaces K - 1) ) *
        ( ((Gammaℝ (s + 1))⁻¹) ^ nrComplexPlaces K *
          (Gammaℝ (s + 1)) ^ nrComplexPlaces K ) := by ring
    _ = 1 := by rw [hDcancel, hshift, hGcancel, hG1cancel]; ring

/-- An entire regularization of the ordinary Dedekind zeta function. -/
def dedekindZetaRegularized (s : ℂ) : ℂ :=
  inverseCompletedMultiplier K s *
    GlobalContinuation.completedZetaPoleRemoved K s

theorem dedekindZetaRegularized_analyticOn :
    AnalyticOnNhd ℂ (dedekindZetaRegularized K) Set.univ := by
  unfold dedekindZetaRegularized
  exact (inverseCompletedMultiplier_analyticOn K).mul
    (GlobalContinuation.completedZetaPoleRemoved_analyticOn K)

/-- On the defining half-plane, the regularization equals `(s-1) ζ_K(s)`.
Thus the entire function above is a genuine continuation of the pole-removed
Dedekind zeta, with no field-specific analytic assumption. -/
theorem dedekindZetaRegularized_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaRegularized K s =
      (s - 1) * NumberField.dedekindZeta K s := by
  rw [dedekindZetaRegularized,
    GlobalContinuation.completedZetaPoleRemoved_eq_zeta K hs]
  calc
    inverseCompletedMultiplier K s *
        (s * (s - 1) * (ZInfty K s * NumberField.dedekindZeta K s))
      = (inverseCompletedMultiplier K s * (s * ZInfty K s)) *
          ((s - 1) * NumberField.dedekindZeta K s) := by ring
    _ = (s - 1) * NumberField.dedekindZeta K s := by
      rw [inverseCompletedMultiplier_mul K hs]
      ring

end
end DedekindZeta.ZetaRegularization
