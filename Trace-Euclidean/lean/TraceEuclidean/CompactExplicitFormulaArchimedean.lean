import TraceEuclidean.CompactExplicitFormulaEndpoint
import TraceEuclidean.OdlyzkoArchimedeanShift

/-!
# Archimedean term for compact explicit-formula kernels

This module evaluates the real-place Gamma factor for an arbitrary normalized
compact source kernel.  The result is kept as a single positive-half-line
Gauss integral, which is the form needed for the Poitou cutoff limit.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)

@[fun_prop]
theorem criticalReal_continuous : Continuous Q.criticalReal := by
  exact Complex.continuous_re.comp
    (Q.phi_differentiable.continuous.comp (by fun_prop))

@[fun_prop]
theorem criticalReal_measurable : Measurable Q.criticalReal :=
  Q.criticalReal_continuous.measurable

/-- Fourth-power decay gives the quadratic spectral moment used in Gauss'
integral formula. -/
theorem criticalReal_mul_sq_integrable :
    Integrable (fun t : ℝ ↦ t ^ 2 * Q.criticalReal t) volume := by
  obtain ⟨D, hD, hDecay⟩ := Q.phi_exists_wideFourthPowerBound
  apply (odlyzkoCriticalMajorant_two_integrable D).mono'
  · exact ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 2)).mul
      Q.criticalReal_continuous).aestronglyMeasurable
  · filter_upwards with t
    let u : ℝ := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have ht : |t| ^ 2 ≤ u ^ 2 := by
      dsimp [u]
      nlinarith [abs_nonneg t]
    have hphi := hDecay (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      (by norm_num [Complex.mul_re]) (by norm_num [Complex.mul_re])
    have hfirst : |t| ^ 2 * |Q.criticalReal t| ≤ |t| ^ 2 * (D / u ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg |t|)
      calc
        |Q.criticalReal t| ≤ ‖Q.phi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
          Complex.abs_re_le_norm _
        _ ≤ D / u ^ 4 := by simpa [u, Complex.mul_im] using hphi
    have hsecond : |t| ^ 2 * (D / u ^ 4) ≤ D / u ^ 2 := by
      rw [show |t| ^ 2 * (D / u ^ 4) = (|t| ^ 2 * D) / u ^ 4 by ring]
      rw [div_le_div_iff₀ (pow_pos hu 4) (pow_pos hu 2)]
      nlinarith [mul_nonneg (mul_nonneg hD (sq_nonneg u))
        (sub_nonneg.mpr ht)]
    calc
      ‖t ^ 2 * Q.criticalReal t‖ = |t| ^ 2 * |Q.criticalReal t| := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ |t| ^ 2 * (D / u ^ 4) := hfirst
      _ ≤ D / u ^ 2 := hsecond
      _ = D / (1 + |t|) ^ 2 := by rfl

/-- The total mass of a normalized compact transform. -/
theorem criticalReal_integral (hQ0 : Q.kernel 0 = 1) :
    (∫ t : ℝ, Q.criticalReal t) = 2 * Real.pi := by
  simpa [hQ0] using Q.criticalReal_cosine_inversion 0

/-- The oscillatory remainder is bounded by the separated quadratic
majorant used in the product-integrability proof. -/
theorem digammaRemainder_norm_le
    (a u t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖Q.criticalReal u *
        odlyzkoDigammaRemainder a t x‖ ≤
      ‖t ^ 2 * Q.criticalReal u‖ *
        ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by
  have hdenpos : 0 < 1 - Real.exp (-x) := by
    have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    linarith
  have hcos0 : 0 ≤ 1 - Real.cos (t * x) := by
    linarith [Real.cos_le_one (t * x)]
  have hcos2 : 1 - Real.cos (t * x) ≤ (t * x) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t * x)]
  have hrem0 : 0 ≤ odlyzkoDigammaRemainder a t x := by
    unfold odlyzkoDigammaRemainder
    positivity
  have hquad0 :
      0 ≤ (1 / 2 : ℝ) *
        (Real.exp (-(a * x)) * x ^ 2 /
          (1 - Real.exp (-x))) := by positivity
  have hremle :
      odlyzkoDigammaRemainder a t x ≤
        t ^ 2 * ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by
    unfold odlyzkoDigammaRemainder
    rw [div_le_iff₀ hdenpos]
    calc
      Real.exp (-(a * x)) * (1 - Real.cos (t * x)) ≤
          Real.exp (-(a * x)) * ((t * x) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcos2 (Real.exp_pos _).le
      _ = t ^ 2 *
          ((1 / 2 : ℝ) *
            (Real.exp (-(a * x)) * x ^ 2 /
              (1 - Real.exp (-x)))) *
            (1 - Real.exp (-x)) := by
        field_simp [hdenpos.ne']
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrem0,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
  calc
    |Q.criticalReal u| * odlyzkoDigammaRemainder a t x ≤
        |Q.criticalReal u| *
          (t ^ 2 * ((1 / 2 : ℝ) *
            (Real.exp (-(a * x)) * x ^ 2 /
              (1 - Real.exp (-x))))) :=
      mul_le_mul_of_nonneg_left hremle (abs_nonneg _)
    _ = t ^ 2 * |Q.criticalReal u| *
        ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by ring

theorem criticalReal_scaled_mul_sq_integrable (b : ℝ) :
    Integrable
      (fun t : ℝ ↦ (b * t) ^ 2 * Q.criticalReal t) volume := by
  have h := Q.criticalReal_mul_sq_integrable.const_mul (b ^ 2)
  exact h.congr (Filter.Eventually.of_forall fun t ↦ by ring)

/-- Product integrability for Gauss' kernel after a fixed rescaling of the
spectral frequency. -/
theorem critical_mul_digammaKernel_scaled_integrable
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦
        Q.criticalReal z.1 *
          odlyzkoDigammaKernel a (b * z.1) z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hzero : IntegrableOn
      (fun x : ℝ ↦ odlyzkoDigammaKernel a 0 x) (Ioi 0) := by
    simpa [odlyzkoDigammaKernel] using
      DedekindZeta.DigammaIntegral.digammaGaussKernel_integrableOn
        ha0 ha1 0
  have hzeroProd : Integrable
      (fun z : ℝ × ℝ ↦
        Q.criticalReal z.1 *
          odlyzkoDigammaKernel a 0 z.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    Q.criticalReal_integrable.mul_prod hzero
  have hquadratic : Integrable
      (fun x : ℝ ↦
        (1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x))))
      (volume.restrict (Ioi 0)) :=
    (odlyzkoDigammaQuadraticKernel_integrableOn ha0).const_mul (1 / 2)
  have hmajor : Integrable
      (fun z : ℝ × ℝ ↦
        ((b * z.1) ^ 2 * Q.criticalReal z.1) *
          ((1 / 2 : ℝ) *
            (Real.exp (-(a * z.2)) * z.2 ^ 2 /
              (1 - Real.exp (-z.2)))))
      (volume.prod (volume.restrict (Ioi 0))) :=
    (Q.criticalReal_scaled_mul_sq_integrable b).mul_prod hquadratic
  have hremMeas : Measurable
      (fun z : ℝ × ℝ ↦
        odlyzkoDigammaRemainder a (b * z.1) z.2) := by
    unfold odlyzkoDigammaRemainder
    fun_prop
  have hremainder : Integrable
      (fun z : ℝ × ℝ ↦
        Q.criticalReal z.1 *
          odlyzkoDigammaRemainder a (b * z.1) z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
    apply hmajor.mono
    · exact ((Q.criticalReal_measurable.comp measurable_fst).mul
        hremMeas).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_snd
          (μ := volume) (ν := volume.restrict (Ioi 0))).ae
            (ae_restrict_mem measurableSet_Ioi)] with z hz
      calc
        ‖Q.criticalReal z.1 *
            odlyzkoDigammaRemainder a (b * z.1) z.2‖ ≤
            ‖(b * z.1) ^ 2 * Q.criticalReal z.1‖ *
              ((1 / 2 : ℝ) *
                (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                  (1 - Real.exp (-z.2)))) :=
          Q.digammaRemainder_norm_le a z.1 (b * z.1) hz
        _ = ‖((b * z.1) ^ 2 * Q.criticalReal z.1) *
              ((1 / 2 : ℝ) *
                (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                  (1 - Real.exp (-z.2))))‖ := by
          have hdenpos : 0 < 1 - Real.exp (-z.2) := by
            have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
            linarith
          have hquad0 : 0 ≤ (1 / 2 : ℝ) *
              (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                (1 - Real.exp (-z.2))) := by positivity
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sq_nonneg (b * z.1)), abs_of_nonneg hquad0]
  have hsum := hzeroProd.add hremainder
  apply hsum.congr
  filter_upwards [
    (Measure.quasiMeasurePreserving_snd
      (μ := volume) (ν := volume.restrict (Ioi 0))).ae
        (ae_restrict_mem measurableSet_Ioi)] with z hz
  change Q.criticalReal z.1 *
      odlyzkoDigammaKernel a 0 z.2 +
        Q.criticalReal z.1 *
          odlyzkoDigammaRemainder a (b * z.1) z.2 =
    Q.criticalReal z.1 *
      odlyzkoDigammaKernel a (b * z.1) z.2
  rw [odlyzkoDigammaKernel_eq_zero_add_remainder a (b * z.1) hz]
  ring

/-- Fourier inversion for Gauss' kernel with a fixed spectral rescaling. -/
theorem critical_mul_digammaKernel_scaled_inner_integral
    (hQ0 : Q.kernel 0 = 1) (a b x : ℝ) :
    (∫ t : ℝ,
      Q.criticalReal t *
        odlyzkoDigammaKernel a (b * t) x) =
      2 * Real.pi *
        ((Real.exp (-x) -
            Real.exp (-(a * x)) * Q.kernel (b * x)) /
          (1 - Real.exp (-x))) := by
  have hcos : Integrable
      (fun t : ℝ ↦
        Q.criticalReal t * Real.cos ((b * t) * x)) volume := by
    apply Q.criticalReal_integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((b * t) * x)
  have hcosIntegral :
      (∫ t : ℝ,
        Q.criticalReal t * Real.cos ((b * t) * x)) =
        2 * Real.pi * Q.kernel (b * x) := by
    calc
      (∫ t : ℝ,
        Q.criticalReal t * Real.cos ((b * t) * x)) =
          ∫ t : ℝ,
            Q.criticalReal t * Real.cos (t * (b * x)) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [show (b * t) * x = t * (b * x) by ring]
      _ = 2 * Real.pi * Q.kernel (b * x) := by
        simpa [criticalReal] using
          Q.criticalReal_cosine_inversion (b * x)
  have hfirst : Integrable
      (fun t : ℝ ↦
        (Real.exp (-x) / (1 - Real.exp (-x))) *
          Q.criticalReal t) volume :=
    Q.criticalReal_integrable.const_mul _
  have hsecond : Integrable
      (fun t : ℝ ↦
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (Q.criticalReal t * Real.cos ((b * t) * x))) volume :=
    hcos.const_mul _
  calc
    (∫ t : ℝ,
      Q.criticalReal t *
        odlyzkoDigammaKernel a (b * t) x) =
        ∫ t : ℝ,
          (Real.exp (-x) / (1 - Real.exp (-x))) *
              Q.criticalReal t -
            (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
              (Q.criticalReal t * Real.cos ((b * t) * x)) := by
      apply integral_congr_ae
      filter_upwards with t
      unfold odlyzkoDigammaKernel
      ring
    _ = (Real.exp (-x) / (1 - Real.exp (-x))) *
          (∫ t : ℝ, Q.criticalReal t) -
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (∫ t : ℝ,
            Q.criticalReal t * Real.cos ((b * t) * x)) := by
      rw [integral_sub hfirst hsecond, integral_const_mul,
        integral_const_mul]
    _ = 2 * Real.pi *
        ((Real.exp (-x) -
            Real.exp (-(a * x)) * Q.kernel (b * x)) /
          (1 - Real.exp (-x))) := by
      rw [show (∫ t : ℝ, Q.criticalReal t) =
          2 * Real.pi by
        simpa [criticalReal] using Q.criticalReal_integral hQ0,
        hcosIntegral]
      ring

/-- Fubini's theorem for the spectrally rescaled Gauss kernel. -/
theorem critical_mul_digammaKernel_scaled_fubini
    (hQ0 : Q.kernel 0 = 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : ℝ) :
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        Q.criticalReal t *
          odlyzkoDigammaKernel a (b * t) x) =
      2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) -
              Real.exp (-(a * x)) * Q.kernel (b * x)) /
            (1 - Real.exp (-x)) := by
  have hjoint := Q.critical_mul_digammaKernel_scaled_integrable
    ha0 ha1 b
  calc
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        Q.criticalReal t *
          odlyzkoDigammaKernel a (b * t) x) =
        ∫ x in Ioi (0 : ℝ),
          ∫ t : ℝ,
            Q.criticalReal t *
              odlyzkoDigammaKernel a (b * t) x :=
      integral_integral_swap hjoint
    _ = ∫ x in Ioi (0 : ℝ),
        2 * Real.pi *
          ((Real.exp (-x) -
              Real.exp (-(a * x)) * Q.kernel (b * x)) /
            (1 - Real.exp (-x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact Q.critical_mul_digammaKernel_scaled_inner_integral hQ0 a b x
    _ = 2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) -
              Real.exp (-(a * x)) * Q.kernel (b * x)) /
            (1 - Real.exp (-x)) := by
      rw [integral_const_mul]

/-- The Gauss integral attached to the real archimedean place. -/
def realGaussIntegral : ℝ :=
  ∫ x in Ioi (0 : ℝ),
    2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) * Q.kernel x) /
      (1 - Real.exp (-2 * x))

/-- Rescaling the quarter-line Gauss kernel produces the real-place integral. -/
theorem quarterGaussKernel_integral :
    (∫ x in Ioi (0 : ℝ),
      (Real.exp (-x) - Real.exp (-((1 / 4 : ℝ) * x)) *
          Q.kernel ((1 / 2 : ℝ) * x)) /
        (1 - Real.exp (-x))) = Q.realGaussIntegral := by
  let f : ℝ → ℝ := fun x ↦
    (Real.exp (-x) - Real.exp (-((1 / 4 : ℝ) * x)) *
        Q.kernel ((1 / 2 : ℝ) * x)) /
      (1 - Real.exp (-x))
  have hscale := integral_comp_mul_left_Ioi f 0
    (by norm_num : (0 : ℝ) < 2)
  have hscale' :
      (∫ x in Ioi (0 : ℝ), f (2 * x)) =
        (2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ), f x := by
    simpa only [mul_zero] using hscale
  change (∫ x in Ioi (0 : ℝ), f x) = _
  calc
    (∫ x in Ioi (0 : ℝ), f x) =
        2 * ∫ x in Ioi (0 : ℝ), f (2 * x) := by
      rw [hscale']
      norm_num [smul_eq_mul]
      ring
    _ = ∫ x in Ioi (0 : ℝ), 2 * f (2 * x) := by
      rw [integral_const_mul]
    _ = Q.realGaussIntegral := by
      unfold realGaussIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp [f]
      rw [show -(2 * x) = -2 * x by ring,
        show -((1 / 4 : ℝ) * (2 * x)) = -(1 / 2 : ℝ) * x by ring,
        show (1 / 2 : ℝ) * (2 * x) = x by ring]
      ring

/-- The real part of the real-place digamma factor is integrable against a
normalized compact transform. -/
theorem critical_mul_re_digamma_quarter_integrable (hQ0 : Q.kernel 0 = 1) :
    Integrable
      (fun t : ℝ ↦
        Q.criticalReal t *
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) volume := by
  have hjoint := Q.critical_mul_digammaKernel_scaled_integrable
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ)
  have hinner := hjoint.integral_prod_left
  have hconst := Q.criticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  have hsum := hconst.add hinner
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [DedekindZeta.DigammaIntegral.re_digamma_quarter_integral]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x _ ↦ odlyzkoQuarterDigammaKernel_eq t x)]
  rw [integral_const_mul]
  ring

/-- Exact real-place digamma pairing, with the kernel dependence isolated in
`realGaussIntegral`. -/
theorem critical_mul_re_digamma_quarter_integral (hQ0 : Q.kernel 0 = 1) :
    (∫ t : ℝ,
      Q.criticalReal t *
        (Complex.digamma
          ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) =
      2 * Real.pi *
        (-Real.eulerMascheroniConstant + Q.realGaussIntegral) := by
  have hjoint := Q.critical_mul_digammaKernel_scaled_integrable
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ)
  have hinner := hjoint.integral_prod_left
  have hconst := Q.criticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  calc
    (∫ t : ℝ,
      Q.criticalReal t *
        (Complex.digamma
          ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) =
        ∫ t : ℝ,
          (-Real.eulerMascheroniConstant * Q.criticalReal t +
            ∫ x in Ioi (0 : ℝ),
              Q.criticalReal t *
                odlyzkoDigammaKernel (1 / 4 : ℝ)
                  ((1 / 2 : ℝ) * t) x) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [DedekindZeta.DigammaIntegral.re_digamma_quarter_integral]
      rw [setIntegral_congr_fun measurableSet_Ioi
        (fun x _ ↦ odlyzkoQuarterDigammaKernel_eq t x)]
      rw [integral_const_mul]
      ring
    _ = (-Real.eulerMascheroniConstant) *
          (∫ t : ℝ, Q.criticalReal t) +
        ∫ t : ℝ,
          ∫ x in Ioi (0 : ℝ),
            Q.criticalReal t *
              odlyzkoDigammaKernel (1 / 4 : ℝ)
                ((1 / 2 : ℝ) * t) x := by
      rw [integral_add hconst hinner, integral_const_mul]
    _ = 2 * Real.pi *
        (-Real.eulerMascheroniConstant + Q.realGaussIntegral) := by
      rw [Q.criticalReal_integral hQ0,
        Q.critical_mul_digammaKernel_scaled_fubini hQ0
          (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ),
        Q.quarterGaussKernel_integral]
      ring

/-- The real-place Gamma bracket is integrable. -/
theorem critical_mul_realPlaceBracket_integrable (hQ0 : Q.kernel 0 = 1) :
    Integrable
      (fun t : ℝ ↦
        Q.criticalReal t *
          (-Real.log Real.pi +
            (Complex.digamma
              ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) volume := by
  have hconst := Q.criticalReal_integrable.const_mul (-Real.log Real.pi)
  have hsum := hconst.add (Q.critical_mul_re_digamma_quarter_integrable hQ0)
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- Exact real-place Gamma pairing. -/
theorem critical_mul_realPlaceBracket_integral (hQ0 : Q.kernel 0 = 1) :
    (∫ t : ℝ,
      Q.criticalReal t *
        (-Real.log Real.pi +
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) =
      2 * Real.pi *
        (-Real.log Real.pi - Real.eulerMascheroniConstant +
          Q.realGaussIntegral) := by
  have hconst := Q.criticalReal_integrable.const_mul (-Real.log Real.pi)
  calc
    (∫ t : ℝ,
      Q.criticalReal t *
        (-Real.log Real.pi +
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) =
        ∫ t : ℝ,
          (-Real.log Real.pi * Q.criticalReal t +
            Q.criticalReal t *
              (Complex.digamma
                ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) := by
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (-Real.log Real.pi) * (∫ t : ℝ, Q.criticalReal t) +
        ∫ t : ℝ, Q.criticalReal t *
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re := by
      rw [integral_add hconst
        (Q.critical_mul_re_digamma_quarter_integrable hQ0), integral_const_mul]
    _ = _ := by
      rw [Q.criticalReal_integral hQ0,
        Q.critical_mul_re_digamma_quarter_integral hQ0]
      ring

end CompactExplicitFormulaKernel

end
end TraceEuclidean
