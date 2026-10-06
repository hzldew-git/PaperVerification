import TraceEuclidean.GenericExplicitFormulaContour
import TraceEuclidean.OdlyzkoFourthDecayCriterion
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Compactly supported explicit-formula weights

This module packages the analytic facts common to compact regularizations of
an explicit-formula kernel.  A nonnegative even `C⁴` kernel with fixed compact
support, whose exponentially tilted Fourier transforms are nonnegative in the
closed critical strip, produces a `CompletedExplicitFormulaWeight`.

The fourth-power vertical decay is proved internally from compactness and four
integrations by parts.  Consequently a concrete compact regularization only
has to supply its elementary support, smoothness, symmetry, and Fourier
positivity data.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Filter Topology MeasureTheory FourierTransform
open scoped RealInnerProductSpace

/-- Source-side data for a compactly supported explicit-formula kernel. -/
structure CompactExplicitFormulaKernel where
  kernel : ℝ → ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  continuous : Continuous kernel
  nonneg : ∀ x : ℝ, 0 ≤ kernel x
  even : ∀ x : ℝ, kernel (-x) = kernel x
  contDiff_four : ContDiff ℝ 4 kernel
  zero_outside : ∀ {x : ℝ}, radius < |x| → kernel x = 0
  tiltedFourier_re_nonneg_closed : ∀ (a w : ℝ),
    -(1 / 2 : ℝ) ≤ a → a ≤ 1 / 2 →
      0 ≤ (𝓕 (fun x : ℝ ↦
        ((Real.exp (a * x) * kernel x : ℝ) : ℂ)) w).re

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)

/-- Exponentially tilted complex form of the compact kernel. -/
def tilted (a x : ℝ) : ℂ :=
  ((Real.exp (a * x) * Q.kernel x : ℝ) : ℂ)

theorem tilted_continuous (a : ℝ) : Continuous (Q.tilted a) := by
  change Continuous (Complex.ofReal ∘
    fun x : ℝ ↦ Real.exp (a * x) * Q.kernel x)
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      Q.continuous)

theorem kernel_hasCompactSupport : HasCompactSupport Q.kernel := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-Q.radius) Q.radius) isCompact_Icc
  intro x hx
  change -Q.radius ≤ x ∧ x ≤ Q.radius
  rw [← abs_le]
  by_contra hbound
  exact hx (Q.zero_outside (lt_of_not_ge hbound))

theorem tilted_hasCompactSupport (a : ℝ) :
    HasCompactSupport (Q.tilted a) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-Q.radius) Q.radius) isCompact_Icc
  intro x hx
  change -Q.radius ≤ x ∧ x ≤ Q.radius
  rw [← abs_le]
  by_contra hbound
  apply hx
  simp [tilted, Q.zero_outside (lt_of_not_ge hbound)]

theorem tilted_integrable (a : ℝ) :
    Integrable (Q.tilted a) volume :=
  (Q.tilted_continuous a).integrable_of_hasCompactSupport
    (Q.tilted_hasCompactSupport a)

/-- Source-normalized bilateral Laplace transform. -/
def phi (s : ℂ) : ℂ :=
  ∫ x : ℝ, (Q.kernel x : ℂ) *
    Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))

theorem phi_eq_fourier (s : ℂ) :
    Q.phi s =
      𝓕 (Q.tilted (s.re - 1 / 2))
        (-s.im / (2 * Real.pi)) := by
  rw [phi, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hexp :
      Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) =
        Complex.exp ((((s.re - 1 / 2) * x : ℝ) : ℂ)) *
          Complex.exp (((s.im * x : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext
    · norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re]
    · norm_num [Complex.mul_im, Complex.sub_im, Complex.add_im]
  have hfreq :
      ((-2 * Real.pi * x * (-s.im / (2 * Real.pi)) : ℝ) : ℂ) *
          Complex.I =
        ((s.im * x : ℝ) : ℂ) * Complex.I := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp, hfreq, ← Complex.ofReal_exp]
  simp only [tilted, Complex.ofReal_mul]
  ring

/-- Positive measure attached to the compact kernel. -/
def kernelMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x : ℝ ↦ ENNReal.ofReal (Q.kernel x))

private theorem kernelDensity_measurable :
    Measurable (fun x : ℝ ↦ ENNReal.ofReal (Q.kernel x)) :=
  Q.continuous.measurable.ennreal_ofReal

private theorem kernelDensity_lt_top :
    ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (Q.kernel x) < ⊤ :=
  Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

theorem kernelMeasure_exp_integrable (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) Q.kernelMeasure := by
  rw [kernelMeasure,
    integrable_withDensity_iff Q.kernelDensity_measurable
      Q.kernelDensity_lt_top]
  have hc : Continuous (fun x : ℝ ↦
      Q.kernel x * Real.exp (t * x)) :=
    Q.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport (fun x : ℝ ↦
      Q.kernel x * Real.exp (t * x)) :=
    Q.kernel_hasCompactSupport.mul_right
  have hi : Integrable (fun x : ℝ ↦
      Q.kernel x * Real.exp (t * x)) volume :=
    hc.integrable_of_hasCompactSupport hs
  have heq :
      (fun x : ℝ ↦ Real.exp (t * x) *
        (ENNReal.ofReal (Q.kernel x)).toReal) =
      (fun x : ℝ ↦ Q.kernel x * Real.exp (t * x)) := by
    funext x
    simp [ENNReal.toReal_ofReal (Q.nonneg x), mul_comm]
  rw [heq]
  exact hi

private theorem kernelMeasure_integrableExpSet :
    ProbabilityTheory.integrableExpSet id Q.kernelMeasure = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact Q.kernelMeasure_exp_integrable t

theorem phi_eq_complexMGF (s : ℂ) :
    Q.phi s =
      ProbabilityTheory.complexMGF id Q.kernelMeasure
        (s - (1 / 2 : ℂ)) := by
  rw [phi, ProbabilityTheory.complexMGF, kernelMeasure,
    integral_withDensity_eq_integral_toReal_smul
      Q.kernelDensity_measurable Q.kernelDensity_lt_top]
  apply integral_congr_ae
  filter_upwards with x
  simp [ENNReal.toReal_ofReal (Q.nonneg x)]

theorem phi_differentiable : Differentiable ℂ Q.phi := by
  have hMGF : Differentiable ℂ
      (ProbabilityTheory.complexMGF id Q.kernelMeasure) := by
    intro z
    have hz : z.re ∈ interior
        (ProbabilityTheory.integrableExpSet id Q.kernelMeasure) := by
      rw [Q.kernelMeasure_integrableExpSet]
      simp
    exact (ProbabilityTheory.hasDerivAt_complexMGF hz).differentiableAt
  have hshift : Differentiable ℂ
      (fun s : ℂ ↦ s - (1 / 2 : ℂ)) :=
    differentiable_id.sub (differentiable_const _)
  simpa only [Function.comp_def, ← Q.phi_eq_complexMGF] using
    hMGF.comp hshift

theorem phi_one_sub (s : ℂ) : Q.phi (1 - s) = Q.phi s := by
  unfold phi
  calc
    (∫ x : ℝ, (Q.kernel x : ℂ) *
        Complex.exp (((1 - s) - (1 / 2 : ℂ)) * (x : ℂ))) =
      ∫ x : ℝ, (Q.kernel (-x) : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Q.even]
      congr 1
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, (Q.kernel x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
      exact integral_neg_eq_self
        (fun x : ℝ ↦ (Q.kernel x : ℂ) *
          Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) volume

theorem phi_re_nonneg_closedStrip (s : ℂ)
    (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1) :
    0 ≤ (Q.phi s).re := by
  rw [Q.phi_eq_fourier]
  apply Q.tiltedFourier_re_nonneg_closed <;> linarith

theorem tilted_contDiff_four (a : ℝ) :
    ContDiff ℝ 4 (Q.tilted a) := by
  have hReal : ContDiff ℝ 4
      (fun x : ℝ ↦ Real.exp (a * x) * Q.kernel x) :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
      Q.contDiff_four)
  change ContDiff ℝ 4 (fun x : ℝ ↦
    ((Real.exp (a * x) * Q.kernel x : ℝ) : ℂ))
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp hReal

private theorem fourth_iteratedDeriv_ofReal (f : ℝ → ℝ)
    (hf : ContDiff ℝ 4 f) (k : ℕ) (hk : k ≤ 4) :
    iteratedDeriv k (fun x : ℝ ↦ (f x : ℂ)) =
      fun x : ℝ ↦ ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < 4 := Nat.lt_of_succ_le hk
      have hk'' : (k : WithTop ℕ∞) < 4 := by exact_mod_cast hk'
      rw [iteratedDeriv_succ, ih hk'.le]
      funext x
      have hd := (hf.differentiable_iteratedDeriv k hk'' x).hasDerivAt
      simpa only [iteratedDeriv_succ] using
        (HasDerivAt.ofReal_comp hd).deriv

private theorem tilted_fourth_deriv_formula (a x : ℝ) :
    iteratedDeriv 4 (Q.tilted a) x =
      ((∑ i ∈ Finset.range 5,
        (Nat.choose 4 i : ℝ) * a ^ i * Real.exp (a * x) *
          iteratedDeriv (4 - i) Q.kernel x : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun y ↦ Real.exp (a * y) * Q.kernel y
  have hf : ContDiff ℝ 4 f :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
      Q.contDiff_four)
  have hCast := congrFun
    (fourth_iteratedDeriv_ofReal f hf 4 (by norm_num)) x
  have hMul : iteratedDeriv 4 f x =
      ∑ i ∈ Finset.range 5,
        (Nat.choose 4 i : ℝ) * a ^ i * Real.exp (a * x) *
          iteratedDeriv (4 - i) Q.kernel x := by
    dsimp [f]
    change iteratedDeriv 4
      ((fun y : ℝ ↦ Real.exp (a * y)) * Q.kernel) x = _
    rw [iteratedDeriv_mul (f := fun y : ℝ ↦ Real.exp (a * y))
      (g := Q.kernel) (n := 4)
      (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id)).contDiffAt
      Q.contDiff_four.contDiffAt]
    simp only [iteratedDeriv_exp_const_mul]
    congr 1
    ext i
    ring
  change iteratedDeriv 4 (fun y : ℝ ↦ ((f y : ℝ) : ℂ)) x = _
  rw [hCast, hMul]

private theorem tilted_continuous_joint :
    Continuous (fun p : ℝ × ℝ ↦ Q.tilted p.1 p.2) := by
  unfold tilted
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp
      (continuous_fst.mul continuous_snd)).mul
        (Q.continuous.comp continuous_snd))

private theorem tilted_fourth_deriv_continuous_joint :
    Continuous (fun p : ℝ × ℝ ↦
      iteratedDeriv 4 (Q.tilted p.1) p.2) := by
  have hReal : Continuous (fun p : ℝ × ℝ ↦
      ∑ i ∈ Finset.range 5,
        (Nat.choose 4 i : ℝ) * p.1 ^ i * Real.exp (p.1 * p.2) *
          iteratedDeriv (4 - i) Q.kernel p.2) := by
    apply continuous_finsetSum _
    intro i _
    have hfi : Continuous (fun p : ℝ × ℝ ↦
        iteratedDeriv (4 - i) Q.kernel p.2) :=
      (Q.contDiff_four.continuous_iteratedDeriv (4 - i)
        (by exact_mod_cast Nat.sub_le 4 i)).comp continuous_snd
    exact (((continuous_const.mul (continuous_fst.pow i)).mul
      (Real.continuous_exp.comp
        (continuous_fst.mul continuous_snd))).mul hfi)
  have hComplex := Complex.continuous_ofReal.comp hReal
  convert hComplex using 1
  funext p
  simpa only [Function.comp_apply] using
    Q.tilted_fourth_deriv_formula p.1 p.2

private theorem tilted_iteratedDeriv_zero_outside
    (a : ℝ) (k : ℕ) {x : ℝ} (hx : Q.radius < |x|) :
    iteratedDeriv k (Q.tilted a) x = 0 := by
  have hOpen : IsOpen {y : ℝ | Q.radius < |y|} :=
    isOpen_lt continuous_const continuous_abs
  have hLocal : Q.tilted a =ᶠ[𝓝 x] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hOpen.mem_nhds hx] with y hy
    simp [tilted, Q.zero_outside hy]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hLocal]
  simp

private theorem tilted_iteratedDeriv_norm_integral_eq_set
    (a : ℝ) (k : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv k (Q.tilted a) x‖) =
      ∫ x in Set.Icc (-Q.radius) Q.radius,
        ‖iteratedDeriv k (Q.tilted a) x‖ := by
  rw [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    MeasurableSet.univ (Set.subset_univ _)
  intro x hx
  have hbound : Q.radius < |x| := by
    by_contra h
    apply hx.2
    change -Q.radius ≤ x ∧ x ≤ Q.radius
    rw [← abs_le]
    exact le_of_not_gt h
  rw [Q.tilted_iteratedDeriv_zero_outside a k hbound, norm_zero]

private theorem hasCompactSupport_iteratedDeriv
    (f : ℝ → ℂ) (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem tilted_iteratedDeriv_integrable
    (a : ℝ) (k : ℕ) (hk : (k : ℕ∞) ≤ 4) :
    Integrable (iteratedDeriv k (Q.tilted a)) volume := by
  have hk' : (k : WithTop ℕ∞) ≤ 4 := by exact_mod_cast hk
  exact ((Q.tilted_contDiff_four a).continuous_iteratedDeriv k hk').integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv (Q.tilted a)
      (Q.tilted_hasCompactSupport a) k)

private theorem exists_uniform_fourth_mass_on (a₀ a₁ : ℝ) :
    ∃ M₀ M₄ : ℝ, ∀ a : ℝ, a₀ ≤ a → a ≤ a₁ →
      (∫ x : ℝ, ‖Q.tilted a x‖) ≤ M₀ ∧
      (∫ x : ℝ, ‖iteratedDeriv 4 (Q.tilted a) x‖) ≤ M₄ := by
  let S : Set (ℝ × ℝ) :=
    Set.Icc a₀ a₁ ×ˢ Set.Icc (-Q.radius) Q.radius
  have hCompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hCompact.exists_bound_of_continuousOn
    Q.tilted_continuous_joint.continuousOn
  obtain ⟨C₄, hC₄⟩ := hCompact.exists_bound_of_continuousOn
    Q.tilted_fourth_deriv_continuous_joint.continuousOn
  let V : ℝ := (volume (Set.Icc (-Q.radius) Q.radius)).toReal
  refine ⟨C₀ * V, C₄ * V, ?_⟩
  intro a ha₀ ha₁
  have ha : a ∈ Set.Icc a₀ a₁ := ⟨ha₀, ha₁⟩
  have hfinite : volume (Set.Icc (-Q.radius) Q.radius) < ⊤ :=
    isCompact_Icc.measure_lt_top
  constructor
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-Q.radius) Q.radius)
      (f := fun x : ℝ ↦ ‖Q.tilted a x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)] using
            hC₀ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    have hEq := Q.tilted_iteratedDeriv_norm_integral_eq_set a 0
    simp only [iteratedDeriv_zero] at hEq
    rw [hEq]
    exact (le_abs_self
      (∫ x in Set.Icc (-Q.radius) Q.radius, ‖Q.tilted a x‖)).trans hb
  · have hb := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (-Q.radius) Q.radius)
      (f := fun x : ℝ ↦
        ‖iteratedDeriv 4 (Q.tilted a) x‖)
      hfinite (by
        intro x hx
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)] using
            hC₄ (a, x) (show (a, x) ∈ S from ⟨ha, hx⟩))
    rw [Q.tilted_iteratedDeriv_norm_integral_eq_set a 4]
    exact (le_abs_self
      (∫ x in Set.Icc (-Q.radius) Q.radius,
        ‖iteratedDeriv 4 (Q.tilted a) x‖)).trans hb

theorem phi_exists_wideFourthPowerBound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ,
      -1 ≤ s.re → s.re ≤ 2 →
        ‖Q.phi s‖ ≤ D / (1 + |s.im|) ^ 4 := by
  obtain ⟨M₀, M₄, hMass⟩ :=
    Q.exists_uniform_fourth_mass_on (-(3 / 2 : ℝ)) (3 / 2 : ℝ)
  obtain ⟨h₀, h₄⟩ := hMass 0 (by norm_num) (by norm_num)
  have hM₀ : 0 ≤ M₀ :=
    (integral_nonneg (fun x ↦ norm_nonneg (Q.tilted 0 x))).trans h₀
  have hM₄ : 0 ≤ M₄ :=
    (integral_nonneg (fun x ↦ norm_nonneg
      (iteratedDeriv 4 (Q.tilted 0) x))).trans h₄
  refine ⟨8 * (M₀ + M₄), by positivity, ?_⟩
  intro s hs₀ hs₁
  let a : ℝ := s.re - 1 / 2
  let w : ℝ := -s.im / (2 * Real.pi)
  let f : ℝ → ℂ := Q.tilted a
  obtain ⟨hMass₀, hMass₄⟩ := hMass a
    (by dsimp [a]; linarith) (by dsimp [a]; linarith)
  have hSmooth : ContDiff ℝ 4 f := by
    simpa only [f] using Q.tilted_contDiff_four a
  have hInt : ∀ k : ℕ, (k : ℕ∞) ≤ 4 →
      Integrable (iteratedDeriv k f) volume := by
    intro k hk
    simpa only [f] using Q.tilted_iteratedDeriv_integrable a k hk
  have hPhi : Q.phi s = 𝓕 f w := by
    simpa only [a, w, f] using Q.phi_eq_fourier s
  have hZero : ‖Q.phi s‖ ≤ M₀ := by
    rw [hPhi]
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) f w).trans hMass₀
  have hFourth : |s.im| ^ 4 * ‖Q.phi s‖ ≤ M₄ := by
    have h := fourier_fourth_frequency_bound f hSmooth hInt w
    rw [odlyzko_fourth_frequency_normalization s.im, ← hPhi] at h
    exact h.trans hMass₄
  have hPow : (1 + |s.im|) ^ 4 ≤ 8 * (1 + |s.im| ^ 4) := by
    have hFactor : 0 ≤ (|s.im| - 1) ^ 2 *
        (7 * |s.im| ^ 2 + 10 * |s.im| + 7) := by positivity
    nlinarith
  have hProduct :
      (1 + |s.im|) ^ 4 * ‖Q.phi s‖ ≤ 8 * (M₀ + M₄) := by
    calc
      _ ≤ (8 * (1 + |s.im| ^ 4)) * ‖Q.phi s‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ = 8 * (‖Q.phi s‖ + |s.im| ^ 4 * ‖Q.phi s‖) := by ring
      _ ≤ 8 * (M₀ + M₄) := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < (1 + |s.im|) ^ 4)).2
  nlinarith

/-- Every compact kernel satisfying the source-side positivity hypotheses
produces all analytic data required by the completed-zeta contour theorem. -/
def toCompletedExplicitFormulaWeight : CompletedExplicitFormulaWeight where
  phi := Q.phi
  differentiable := Q.phi_differentiable
  one_sub := Q.phi_one_sub
  re_nonneg_closedStrip := Q.phi_re_nonneg_closedStrip
  wideFourthPowerBound := Q.phi_exists_wideFourthPowerBound

end CompactExplicitFormulaKernel

end
end TraceEuclidean
