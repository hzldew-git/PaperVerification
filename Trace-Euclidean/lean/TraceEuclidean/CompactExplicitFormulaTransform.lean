import TraceEuclidean.CompactExplicitFormulaWeight
import TraceEuclidean.OdlyzkoCriticalTransform

/-!
# Fourier inversion for compact explicit-formula kernels

This module supplies the source-side transform facts needed to identify the
endpoint, prime-ideal, and archimedean terms of the generic completed-zeta
contour formula.  The normalisation agrees with `CompactExplicitFormulaKernel.phi`.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Filter Topology MeasureTheory FourierTransform
open scoped RealInnerProductSpace ComplexConjugate

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)

/-- The compact source transform is integrable on every vertical line used by
the completed-zeta contour. -/
theorem phi_vertical_integrable (sigma : ℝ)
    (hsigma0 : -1 ≤ sigma) (hsigma1 : sigma ≤ 2) :
    Integrable
      (fun t : ℝ ↦ Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I)) volume := by
  obtain ⟨D, -, hDecay⟩ := Q.phi_exists_wideFourthPowerBound
  apply (odlyzkoCriticalMajorant_integrable D).mono'
  · exact (Q.phi_differentiable.continuous.comp
      (by fun_prop : Continuous
        (fun t : ℝ ↦ (sigma : ℂ) + (t : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards with t
    have h := hDecay ((sigma : ℂ) + (t : ℂ) * Complex.I)
      (by norm_num [Complex.mul_re]; exact hsigma0)
      (by norm_num [Complex.mul_re]; exact hsigma1)
    simpa [Complex.mul_im] using h

/-- The Fourier transform of every exponential tilt needed between the lines
`Re(s)=-1` and `Re(s)=2` is integrable. -/
theorem tilted_fourier_integrable (a : ℝ)
    (ha0 : -(3 / 2 : ℝ) ≤ a) (ha1 : a ≤ 3 / 2) :
    Integrable (𝓕 (Q.tilted a)) volume := by
  let sigma : ℝ := a + 1 / 2
  have hscaled := (Q.phi_vertical_integrable sigma (by dsimp [sigma]; linarith)
      (by dsimp [sigma]; linarith)).comp_mul_left'
    (show (-2 * Real.pi : ℝ) ≠ 0 by positivity)
  apply hscaled.congr
  filter_upwards with w
  have hre :
      (((sigma : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).re -
          1 / 2) = a := by
    norm_num [sigma, Complex.mul_re]
  have him :
      -((sigma : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).im /
          (2 * Real.pi) = w := by
    norm_num [Complex.mul_im]
  simpa only [hre, him] using
    Q.phi_eq_fourier
      ((sigma : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I)

/-- Fourier inversion for a permitted exponential tilt. -/
theorem tilted_fourierInv_fourier (a x : ℝ)
    (ha0 : -(3 / 2 : ℝ) ≤ a) (ha1 : a ≤ 3 / 2) :
    𝓕⁻ (𝓕 (Q.tilted a)) x = Q.tilted a x := by
  exact congrFun
    ((Q.tilted_continuous a).fourierInv_fourier_eq
      (Q.tilted_integrable a)
      (Q.tilted_fourier_integrable a ha0 ha1)) x

/-- Fourier inversion for a fixed tilt, written as an ordinary complex
integral. -/
theorem tilted_fourier_inversion_integral (a x : ℝ)
    (ha0 : -(3 / 2 : ℝ) ≤ a) (ha1 : a ≤ 3 / 2) :
    (∫ w : ℝ,
        Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
          𝓕 (Q.tilted a) w) =
      Q.tilted a x := by
  have h := Q.tilted_fourierInv_fourier a x ha0 ha1
  rw [Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul, RCLike.inner_apply, conj_trivial, mul_assoc,
    mul_comm, mul_left_comm] using h

/-- A fixed Fourier phase preserves vertical-line integrability. -/
theorem phi_vertical_phase_integrable (sigma x : ℝ)
    (hsigma0 : -1 ≤ sigma) (hsigma1 : sigma ≤ 2) :
    Integrable
      (fun t : ℝ ↦
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hprod : Integrable
      (fun t : ℝ ↦
        Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I)) volume := by
    apply (Q.phi_vertical_integrable sigma hsigma0 hsigma1).mul_bdd (c := 1)
    · exact (by fun_prop : Continuous
        (fun t : ℝ ↦
          Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
    · filter_upwards with t
      rw [Complex.norm_exp]
      norm_num
  exact hprod.congr (Filter.Eventually.of_forall fun t ↦ by ring)

/-- Fourier inversion in the source vertical-line parameter. -/
theorem phi_vertical_inversion_integral (sigma x : ℝ)
    (hsigma0 : -1 ≤ sigma) (hsigma1 : sigma ≤ 2) :
    (∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I)) =
      (2 * Real.pi : ℝ) • Q.tilted (sigma - 1 / 2) x := by
  let a : ℝ := -1 / (2 * Real.pi)
  let g : ℝ → ℂ := fun w ↦
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (Q.tilted (sigma - 1 / 2)) w
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hpoint (t : ℝ) :
      Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I) =
        g (a * t) := by
    have hat : a * t = -t / (2 * Real.pi) := by
      dsimp [a]
      field_simp [Real.pi_ne_zero]
    have hre :
        (((sigma : ℂ) + (t : ℂ) * Complex.I).re - 1 / 2) =
          sigma - 1 / 2 := by norm_num [Complex.mul_re]
    have him :
        -((sigma : ℂ) + (t : ℂ) * Complex.I).im / (2 * Real.pi) =
          -t / (2 * Real.pi) := by
      norm_num [Complex.mul_im]
    dsimp [g]
    rw [hat, ← show
      Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I) =
        𝓕 (Q.tilted (sigma - 1 / 2)) (-t / (2 * Real.pi)) by
          simpa only [hre, him] using
            Q.phi_eq_fourier
              ((sigma : ℂ) + (t : ℂ) * Complex.I)]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  have habs : |a⁻¹| = 2 * Real.pi := by
    dsimp [a]
    rw [inv_div]
    rw [show (2 * Real.pi : ℝ) / (-1) = -(2 * Real.pi) by ring,
      abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    (∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi ((sigma : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ, g (a * t) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = |a⁻¹| • ∫ w : ℝ, g w := Measure.integral_comp_mul_left g a
    _ = (2 * Real.pi : ℝ) • Q.tilted (sigma - 1 / 2) x := by
      rw [habs]
      change (2 * Real.pi : ℝ) •
          (∫ w : ℝ,
            Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
              𝓕 (Q.tilted (sigma - 1 / 2)) w) = _
      rw [Q.tilted_fourier_inversion_integral]
      · linarith
      · linarith

/-- The compact transform commutes with complex conjugation. -/
theorem phi_conj (s : ℂ) : Q.phi (conj s) = conj (Q.phi s) := by
  unfold phi
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_sub, map_div₀, map_ofNat]
  simp

/-- The compact transform is real on the critical line. -/
theorem phi_critical_im_eq_zero (t : ℝ) :
    (Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hone : 1 - s = starRingEnd ℂ s := by
    dsimp [s]
    apply Complex.ext
    · norm_num
    · simp
  apply Complex.conj_eq_iff_im.mp
  calc
    starRingEnd ℂ (Q.phi s) = Q.phi (starRingEnd ℂ s) := by
      simpa using (Q.phi_conj s).symm
    _ = Q.phi (1 - s) := by rw [hone]
    _ = Q.phi s := Q.phi_one_sub s

/-- Real critical-line transform used in the source-side formula. -/
def criticalReal (t : ℝ) : ℝ :=
  (Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re

theorem criticalReal_integrable : Integrable Q.criticalReal volume := by
  have h := Q.phi_vertical_integrable (1 / 2) (by norm_num) (by norm_num)
  change Integrable (fun t : ℝ ↦
    (Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re) volume
  exact h.re

/-- Critical-line cosine inversion in the source normalization. -/
theorem criticalReal_cosine_inversion (x : ℝ) :
    (∫ t : ℝ, Q.criticalReal t * Real.cos (t * x)) =
      2 * Real.pi * Q.kernel x := by
  have h := congrArg Complex.re
    (Q.phi_vertical_inversion_integral (1 / 2) x (by norm_num) (by norm_num))
  have hre := integral_re
    (Q.phi_vertical_phase_integrable (1 / 2) x (by norm_num) (by norm_num))
  have hreal :
      (∫ t : ℝ,
        (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re) =
        (2 * Real.pi * Q.kernel x : ℝ) := by
    exact hre.trans (by simpa [tilted] using h)
  calc
    (∫ t : ℝ, Q.criticalReal t * Real.cos (t * x)) =
        ∫ t : ℝ,
          (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
            Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Complex.mul_re, Q.phi_critical_im_eq_zero]
      simp only [criticalReal, mul_zero, sub_zero, Complex.exp_re]
      simp [Real.cos_neg]
      ring
    _ = 2 * Real.pi * Q.kernel x := hreal

end CompactExplicitFormulaKernel

end
end TraceEuclidean
