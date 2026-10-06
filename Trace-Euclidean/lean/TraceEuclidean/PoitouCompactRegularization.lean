import TraceEuclidean.CompactExplicitFormulaWeight
import TraceEuclidean.PoitouGaussianRegularization
import TraceEuclidean.OdlyzkoCriticalTransform

/-!
# Compact regularization of the Poitou kernel

The scaled `b = 4` Odlyzko kernel is used only as a positive Fourier cutoff.
For every positive cutoff radius the product with Poitou's kernel is compactly
supported, `C⁴`, even, nonnegative, and Fourier-positive after every tilt in
the closed critical strip.  It therefore gives an unconditional instance of
the generic completed-zeta contour theorem.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform Complex Set
open scoped Convolution RealInnerProductSpace

/-- Positive compact cutoff, tending pointwise to one as `R → ∞`. -/
def poitouCompactCutoff (R x : ℝ) : ℝ :=
  TraceEuclidean.odlyzkoF4 (x / R)

def poitouCompactCutoffComplex (R x : ℝ) : ℂ :=
  poitouCompactCutoff R x

theorem poitouCompactCutoff_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (poitouCompactCutoff R) := by
  unfold poitouCompactCutoff
  exact TraceEuclidean.odlyzkoF4_continuous.comp
    (continuous_id.div_const R)

theorem poitouCompactCutoffComplex_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (poitouCompactCutoffComplex R) := by
  change Continuous (Complex.ofReal ∘ poitouCompactCutoff R)
  exact Complex.continuous_ofReal.comp (poitouCompactCutoff_continuous hR)

theorem poitouCompactCutoff_nonneg (R x : ℝ) :
    0 ≤ poitouCompactCutoff R x :=
  TraceEuclidean.odlyzkoF4_nonneg _

theorem poitouCompactCutoff_even (R x : ℝ) :
    poitouCompactCutoff R (-x) = poitouCompactCutoff R x := by
  unfold poitouCompactCutoff
  rw [show -x / R = -(x / R) by ring,
    TraceEuclidean.odlyzkoF4_even]

theorem poitouCompactCutoff_eq_zero_of_radius_lt_abs
    {R x : ℝ} (hR : 0 < R) (hx : 8 * R < |x|) :
    poitouCompactCutoff R x = 0 := by
  apply TraceEuclidean.odlyzkoF4_eq_zero_of_eight_lt_abs
  rw [abs_div, abs_of_pos hR]
  exact (lt_div_iff₀ hR).2 (by simpa [mul_comm] using hx)

theorem poitouCompactCutoff_hasCompactSupport
    {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (poitouCompactCutoff R) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(8 * R)) (8 * R)) isCompact_Icc
  intro x hx
  change -(8 * R) ≤ x ∧ x ≤ 8 * R
  rw [← abs_le]
  by_contra hbound
  exact hx (poitouCompactCutoff_eq_zero_of_radius_lt_abs
    hR (lt_of_not_ge hbound))

theorem poitouCompactCutoffComplex_integrable
    {R : ℝ} (hR : 0 < R) :
    Integrable (poitouCompactCutoffComplex R) volume := by
  exact (poitouCompactCutoffComplex_continuous hR).integrable_of_hasCompactSupport
    (by
      apply HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (-(8 * R)) (8 * R)) isCompact_Icc
      intro x hx
      change -(8 * R) ≤ x ∧ x ≤ 8 * R
      rw [← abs_le]
      by_contra hbound
      apply hx
      simp [poitouCompactCutoffComplex,
        poitouCompactCutoff_eq_zero_of_radius_lt_abs
          hR (lt_of_not_ge hbound)])

theorem poitouCompactCutoff_fourier_eq
    {R : ℝ} (hR : 0 < R) (w : ℝ) :
    𝓕 (poitouCompactCutoffComplex R) w =
      ((R : ℝ) : ℂ) *
        𝓕 TraceEuclidean.odlyzkoF4Complex (R * w) := by
  rw [Real.fourier_real_eq]
  calc
    (∫ x : ℝ, 𝐞 (-(x * w)) • poitouCompactCutoffComplex R x) =
        ∫ x : ℝ, (fun u : ℝ ↦
          𝐞 (-(u * (R * w))) • TraceEuclidean.odlyzkoF4Complex u)
            (x / R) := by
      apply integral_congr_ae
      filter_upwards with x
      change 𝐞 (-(x * w)) •
          (TraceEuclidean.odlyzkoF4 (x / R) : ℂ) = _
      congr 2
      field_simp [hR.ne']
    _ = |R| • ∫ u : ℝ,
        𝐞 (-(u * (R * w))) •
          TraceEuclidean.odlyzkoF4Complex u :=
      Measure.integral_comp_div (fun u : ℝ ↦
        𝐞 (-(u * (R * w))) •
          TraceEuclidean.odlyzkoF4Complex u) R
    _ = ((R : ℝ) : ℂ) *
        𝓕 TraceEuclidean.odlyzkoF4Complex (R * w) := by
      rw [abs_of_pos hR, Real.fourier_real_eq, Complex.real_smul]

private theorem odlyzkoF4Complex_fourier_integrable :
    Integrable (𝓕 TraceEuclidean.odlyzkoF4Complex) volume := by
  have heq : TraceEuclidean.odlyzkoTiltedF4 0 =
      TraceEuclidean.odlyzkoF4Complex := by
    funext x
    simp [TraceEuclidean.odlyzkoTiltedF4,
      TraceEuclidean.odlyzkoF4Complex]
  simpa only [heq] using
    TraceEuclidean.odlyzkoTiltedF4_zero_fourier_integrable

theorem poitouCompactCutoff_fourier_integrable
    {R : ℝ} (hR : 0 < R) :
    Integrable (𝓕 (poitouCompactCutoffComplex R)) volume := by
  have hscaled : Integrable
      (fun w : ℝ ↦ 𝓕 TraceEuclidean.odlyzkoF4Complex (R * w)) volume :=
    odlyzkoF4Complex_fourier_integrable.comp_mul_left' hR.ne'
  have hmul := hscaled.const_mul ((R : ℝ) : ℂ)
  apply hmul.congr
  filter_upwards with w
  exact (poitouCompactCutoff_fourier_eq hR w).symm

theorem poitouCompactCutoff_fourier_re_nonneg
    {R : ℝ} (hR : 0 < R) (w : ℝ) :
    0 ≤ (𝓕 (poitouCompactCutoffComplex R) w).re := by
  rw [poitouCompactCutoff_fourier_eq hR, Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hR.le
    (TraceEuclidean.odlyzkoF4_fourier_re_nonneg (R * w))

theorem poitouCompactCutoff_fourier_im_eq_zero
    {R : ℝ} (hR : 0 < R) (w : ℝ) :
    (𝓕 (poitouCompactCutoffComplex R) w).im = 0 := by
  rw [poitouCompactCutoff_fourier_eq hR, Complex.mul_im]
  simp [TraceEuclidean.odlyzkoF4_fourier_im_eq_zero]

/-- Compactly supported regularization of Poitou's complete kernel. -/
def poitouCompactRegularizedKernel (y R x : ℝ) : ℝ :=
  poitouFullKernel y x * poitouCompactCutoff R x

def poitouCompactRegularizedTiltedKernel
    (y R a x : ℝ) : ℂ :=
  ((Real.exp (a * x) * poitouCompactRegularizedKernel y R x : ℝ) : ℂ)

theorem poitouCompactRegularizedKernel_continuous
    {y R : ℝ} (hR : 0 < R) :
    Continuous (poitouCompactRegularizedKernel y R) :=
  (poitouFullKernel_continuous y).mul
    (poitouCompactCutoff_continuous hR)

theorem poitouCompactRegularizedKernel_nonneg (y R x : ℝ) :
    0 ≤ poitouCompactRegularizedKernel y R x :=
  mul_nonneg (poitouFullKernel_nonneg y x)
    (poitouCompactCutoff_nonneg R x)

theorem poitouCompactRegularizedKernel_even (y R x : ℝ) :
    poitouCompactRegularizedKernel y R (-x) =
      poitouCompactRegularizedKernel y R x := by
  simp only [poitouCompactRegularizedKernel,
    poitouFullKernel_even, poitouCompactCutoff_even]

theorem poitouFullKernel_contDiff_four (y : ℝ) :
    ContDiff ℝ 4 (poitouFullKernel y) := by
  have h := Complex.reCLM.contDiff.comp
    (poitouFullKernelComplex_contDiff_four y)
  simpa only [Function.comp_def, Complex.reCLM_apply,
    poitouFullKernelComplex, ofReal_re] using h

theorem poitouCompactCutoff_contDiff_four
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 4 (poitouCompactCutoff R) := by
  unfold poitouCompactCutoff
  exact TraceEuclidean.odlyzkoF4_contDiff_four.comp
    (contDiff_id.div_const R)

theorem poitouCompactRegularizedKernel_contDiff_four
    {y R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 4 (poitouCompactRegularizedKernel y R) := by
  exact (poitouFullKernel_contDiff_four y).mul
    (poitouCompactCutoff_contDiff_four hR)

theorem poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs
    {y R x : ℝ} (hR : 0 < R) (hx : 8 * R < |x|) :
    poitouCompactRegularizedKernel y R x = 0 := by
  simp [poitouCompactRegularizedKernel,
    poitouCompactCutoff_eq_zero_of_radius_lt_abs hR hx]

theorem poitouCompactRegularizedTiltedKernel_eq_mul
    (y R a x : ℝ) :
    poitouCompactRegularizedTiltedKernel y R a x =
      poitouTiltedFullKernel y a x *
        poitouCompactCutoffComplex R x := by
  simp only [poitouCompactRegularizedTiltedKernel,
    poitouCompactRegularizedKernel, poitouTiltedFullKernel,
    poitouCompactCutoffComplex]
  push_cast
  ring

theorem poitouCompactRegularizedTiltedKernel_integrable
    {y R a : ℝ} (hy : 0 < y) (hR : 0 < R) :
    Integrable (poitouCompactRegularizedTiltedKernel y R a) volume := by
  have hc : Continuous (poitouCompactRegularizedTiltedKernel y R a) := by
    change Continuous (Complex.ofReal ∘ fun x : ℝ ↦
      Real.exp (a * x) * poitouCompactRegularizedKernel y R x)
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
          (poitouCompactRegularizedKernel_continuous hR))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(8 * R)) (8 * R)) isCompact_Icc
  intro x hx
  change -(8 * R) ≤ x ∧ x ≤ 8 * R
  rw [← abs_le]
  by_contra hbound
  apply hx
  simp [poitouCompactRegularizedTiltedKernel,
    poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs
      hR (lt_of_not_ge hbound)]

theorem poitouCompactRegularizedTiltedKernel_fourier_eq_convolution
    {y R a : ℝ} (hy : 0 < y) (hR : 0 < R)
    (ha₀ : -(1 / 2 : ℝ) < a) (ha₁ : a < 1 / 2) (w : ℝ) :
    𝓕 (poitouCompactRegularizedTiltedKernel y R a) w =
      ((𝓕 (poitouCompactCutoffComplex R))
          ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 (poitouTiltedFullKernel y a))) w := by
  calc
    𝓕 (poitouCompactRegularizedTiltedKernel y R a) w =
        𝓕 (fun x ↦ poitouTiltedFullKernel y a x *
          poitouCompactCutoffComplex R x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact poitouCompactRegularizedTiltedKernel_eq_mul y R a x
    _ = _ := TraceEuclidean.fourierMulEqConvolution
      (poitouTiltedFullKernel y a) (poitouCompactCutoffComplex R)
      (poitouTiltedFullKernel_integrable hy ha₀ ha₁)
      (poitouCompactCutoffComplex_integrable hR)
      (poitouCompactCutoff_fourier_integrable hR)
      (poitouCompactCutoffComplex_continuous hR) w

theorem poitouCompactRegularizedTiltedKernel_convolution_integrable
    {y R a : ℝ} (hy : 0 < y) (hR : 0 < R)
    (ha₀ : -(1 / 2 : ℝ) < a) (ha₁ : a < 1 / 2) (w : ℝ) :
    Integrable (fun z : ℝ ↦
      𝓕 (poitouCompactCutoffComplex R) z *
        𝓕 (poitouTiltedFullKernel y a) (w - z)) volume := by
  apply (poitouCompactCutoff_fourier_integrable hR).mul_bdd
  · exact ((VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (poitouTiltedFullKernel_integrable hy ha₀ ha₁)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with z
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) (poitouTiltedFullKernel y a) (w - z)

theorem poitouCompactRegularizedTiltedKernel_fourier_re_nonneg_open
    {y R a : ℝ} (hy : 0 < y) (hR : 0 < R)
    (ha₀ : -(1 / 2 : ℝ) < a) (ha₁ : a < 1 / 2) (w : ℝ) :
    0 ≤ (𝓕 (poitouCompactRegularizedTiltedKernel y R a) w).re := by
  rw [poitouCompactRegularizedTiltedKernel_fourier_eq_convolution
    hy hR ha₀ ha₁ w, MeasureTheory.convolution_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re
    (poitouCompactRegularizedTiltedKernel_convolution_integrable
      hy hR ha₀ ha₁ w)]
  simp only [RCLike.re_eq_complex_re]
  apply integral_nonneg
  intro z
  change 0 ≤ (𝓕 (poitouCompactCutoffComplex R) z *
    𝓕 (poitouTiltedFullKernel y a) (w - z)).re
  rw [Complex.mul_re,
    poitouCompactCutoff_fourier_im_eq_zero hR]
  simp only [zero_mul, sub_zero]
  exact mul_nonneg (poitouCompactCutoff_fourier_re_nonneg hR z)
    (poitouTiltedFullKernel_fourier_re_nonneg
      hy a (w - z) ha₀ ha₁)

private theorem poitouCompactRegularizedTiltedKernel_fourier_eq_setIntegral
    {y R : ℝ} (hR : 0 < R) (a w : ℝ) :
    𝓕 (poitouCompactRegularizedTiltedKernel y R a) w =
      ∫ x in Set.Icc (-(8 * R)) (8 * R),
        Complex.exp
            ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
          poitouCompactRegularizedTiltedKernel y R a x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    MeasurableSet.univ (Set.subset_univ _)
  intro x hx
  have hbound : 8 * R < |x| := by
    by_contra h
    apply hx.2
    change -(8 * R) ≤ x ∧ x ≤ 8 * R
    rw [← abs_le]
    exact le_of_not_gt h
  simp [poitouCompactRegularizedTiltedKernel,
    poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs hR hbound]

private theorem poitouCompactRegularizedTiltedKernel_fourier_continuous
    {y R : ℝ} (hR : 0 < R) (w : ℝ) :
    Continuous (fun a : ℝ ↦
      𝓕 (poitouCompactRegularizedTiltedKernel y R a) w) := by
  have htilt : Continuous (fun p : ℝ × ℝ ↦
      poitouCompactRegularizedTiltedKernel y R p.1 p.2) := by
    unfold poitouCompactRegularizedTiltedKernel
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_fst.mul continuous_snd)).mul
          ((poitouCompactRegularizedKernel_continuous hR).comp
            continuous_snd))
  have hphase : Continuous (fun p : ℝ × ℝ ↦
      Complex.exp
        ((↑(-2 * Real.pi * p.2 * w) : ℂ) * Complex.I)) := by
    fun_prop
  have hwhole : Continuous (fun p : ℝ × ℝ ↦
      Complex.exp
          ((↑(-2 * Real.pi * p.2 * w) : ℂ) * Complex.I) *
        poitouCompactRegularizedTiltedKernel y R p.1 p.2) :=
    hphase.mul htilt
  have hset : Continuous (fun a : ℝ ↦
      ∫ x in Set.Icc (-(8 * R)) (8 * R),
        Complex.exp
            ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
          poitouCompactRegularizedTiltedKernel y R a x) :=
    continuous_parametric_integral_of_continuous hwhole isCompact_Icc
  convert hset using 1
  funext a
  exact poitouCompactRegularizedTiltedKernel_fourier_eq_setIntegral hR a w

theorem poitouCompactRegularizedTiltedKernel_fourier_re_nonneg_closed
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) (a w : ℝ)
    (ha₀ : -(1 / 2 : ℝ) ≤ a) (ha₁ : a ≤ 1 / 2) :
    0 ≤ (𝓕 (poitouCompactRegularizedTiltedKernel y R a) w).re := by
  let S : Set ℝ := {b | 0 ≤
    (𝓕 (poitouCompactRegularizedTiltedKernel y R b) w).re}
  have hS : IsClosed S :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp
        (poitouCompactRegularizedTiltedKernel_fourier_continuous hR w))
  have hsub : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ S := by
    intro b hb
    exact poitouCompactRegularizedTiltedKernel_fourier_re_nonneg_open
      hy hR hb.1 hb.2 w
  have hclosure : closure (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) ⊆ S :=
    (hS.closure_subset_iff).2 hsub
  rw [closure_Ioo (by norm_num : -(1 / 2 : ℝ) ≠ 1 / 2)] at hclosure
  exact hclosure ⟨ha₀, ha₁⟩

/-- The compact Poitou regularization as source data for the generic contour
theorem. -/
def poitouCompactExplicitFormulaKernel
    (y R : ℝ) (hy : 0 < y) (hR : 0 < R) :
    TraceEuclidean.CompactExplicitFormulaKernel where
  kernel := poitouCompactRegularizedKernel y R
  radius := 8 * R
  radius_nonneg := by positivity
  continuous := poitouCompactRegularizedKernel_continuous hR
  nonneg := poitouCompactRegularizedKernel_nonneg y R
  even := poitouCompactRegularizedKernel_even y R
  contDiff_four := poitouCompactRegularizedKernel_contDiff_four hR
  zero_outside := poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs hR
  tiltedFourier_re_nonneg_closed :=
    poitouCompactRegularizedTiltedKernel_fourier_re_nonneg_closed hy hR

/-- Every positive compact cutoff gives an unconditional generic completed
explicit-formula weight. -/
def poitouCompactCompletedWeight
    (y R : ℝ) (hy : 0 < y) (hR : 0 < R) :
    TraceEuclidean.CompletedExplicitFormulaWeight :=
  (poitouCompactExplicitFormulaKernel y R hy hR).toCompletedExplicitFormulaWeight

theorem poitouCompact_completedVerticalPair_integral_re_nonneg
    (y R : ℝ) (hy : 0 < y) (hR : 0 < R)
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (poitouCompactCompletedWeight y R hy hR).completedVerticalPair K t).re :=
  TraceEuclidean.CompletedExplicitFormulaWeight.completedVerticalPair_integral_re_nonneg
      (poitouCompactCompletedWeight y R hy hR) K

end
end TraceEuclidean.PoitouKernel
