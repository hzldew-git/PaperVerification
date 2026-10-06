import TraceEuclidean.PoitouAdmissibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace TraceEuclidean.PoitouKernel

open MeasureTheory Set
open TraceEuclidean.PoitouDegreeEleven
open FourierTransform Complex
open scoped Convolution RealInnerProductSpace

noncomputable section

/-- Autocorrelation of the compact quadratic bump. -/
def poitouBumpAutocorrelation (t : ℝ) : ℝ :=
  ∫ u : ℝ, poitouBump u * poitouBump (t - u)

def poitouAutocorrelationPolynomial (t : ℝ) : ℝ :=
  -3 / 160 * (t - 2) ^ 3 * (t ^ 2 + 6 * t + 4)

private theorem poitouBumpAutocorrelation_integrand_eq_indicator
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    (fun u : ℝ ↦ poitouBump u * poitouBump (t - u)) =
      (Set.Ioc (t - 1) 1).indicator
        (fun u : ℝ ↦ poitouBumpCore u * poitouBumpCore (t - u)) := by
  funext u
  by_cases hu : u ∈ Set.Ioc (t - 1) 1
  · have huBounds : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have htuBounds : |t - u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simp [poitouBump, huBounds, htuBounds, Set.indicator_of_mem hu]
  · simp only [Set.indicator, hu, if_false]
    unfold poitouBump
    split_ifs with huBounds htuBounds
    · have huIcc := abs_le.mp huBounds
      have htuIcc := abs_le.mp htuBounds
      have hueq : u = t - 1 := by
        have hle : t - 1 ≤ u := by linarith [htuIcc.2]
        have hnot : ¬ t - 1 < u := by
          intro hlt
          exact hu ⟨hlt, huIcc.2⟩
        exact le_antisymm (le_of_not_gt hnot) hle
      subst u
      norm_num [poitouBumpCore]
    · simp
    · simp
    · simp

private def poitouBumpAutocorrelationPrimitive (t u : ℝ) : ℝ :=
  3 * t ^ 2 * u ^ 3 / 16 - 9 * t ^ 2 * u / 16 -
    9 * t * u ^ 4 / 32 + 9 * t * u ^ 2 / 16 +
    9 * u ^ 5 / 80 - 3 * u ^ 3 / 8 + 9 * u / 16

private theorem poitouBumpAutocorrelationPrimitive_hasDerivAt
    (t u : ℝ) :
    HasDerivAt (poitouBumpAutocorrelationPrimitive t)
      (poitouBumpCore u * poitouBumpCore (t - u)) u := by
  have h3 := (hasDerivAt_id u).pow 3
  have h4 := (hasDerivAt_id u).pow 4
  have h2 := (hasDerivAt_id u).pow 2
  have h5 := (hasDerivAt_id u).pow 5
  have hraw :=
    ((((((h3.const_mul (3 * t ^ 2 / 16)).sub
      ((hasDerivAt_id u).const_mul (9 * t ^ 2 / 16))).sub
      (h4.const_mul (9 * t / 32))).add
      (h2.const_mul (9 * t / 16))).add
      (h5.const_mul (9 / 80))).sub
      (h3.const_mul (3 / 8))).add
      ((hasDerivAt_id u).const_mul (9 / 16))
  convert hraw using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try funext v
  all_goals try simp only [poitouBumpAutocorrelationPrimitive, Pi.add_apply,
    Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one]
  all_goals try unfold poitouBumpCore
  all_goals try ring

/-- On its positive support half, the bump autocorrelation is the explicit
quintic polynomial used in Poitou's closed `L` function. -/
theorem poitouBumpAutocorrelation_eq_polynomial
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    poitouBumpAutocorrelation t = poitouAutocorrelationPolynomial t := by
  rw [poitouBumpAutocorrelation,
    poitouBumpAutocorrelation_integrand_eq_indicator ht0 ht2,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : t - 1 ≤ (1 : ℝ))]
  have hcont : Continuous
      (fun u : ℝ ↦ poitouBumpCore u * poitouBumpCore (t - u)) := by
    unfold poitouBumpCore
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ poitouBumpAutocorrelationPrimitive_hasDerivAt t u)
    (hcont.intervalIntegrable (t - 1) 1)]
  unfold poitouBumpAutocorrelationPrimitive poitouAutocorrelationPolynomial
  ring

theorem poitouBumpAutocorrelation_integrable :
    Integrable poitouBumpAutocorrelation volume := by
  have h := poitouBump_integrable.integrable_convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) poitouBump_integrable
  exact h.congr (Filter.Eventually.of_forall fun t ↦ by
    simp only [poitouBumpAutocorrelation, MeasureTheory.convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul])

theorem poitouBumpAutocorrelation_hasCompactSupport :
    HasCompactSupport poitouBumpAutocorrelation := by
  have h := poitouBump_hasCompactSupport.convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    poitouBump_hasCompactSupport
  change HasCompactSupport
    (poitouBump ⋆[ContinuousLinearMap.lsmul ℝ ℝ] poitouBump)
  exact h

theorem poitouBumpAutocorrelation_even (t : ℝ) :
    poitouBumpAutocorrelation (-t) = poitouBumpAutocorrelation t := by
  let f : ℝ → ℝ := fun u ↦ poitouBump u * poitouBump (t - u)
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding f
  calc
    poitouBumpAutocorrelation (-t) =
        ∫ u : ℝ, f (-u) := by
      unfold poitouBumpAutocorrelation
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [f]
      rw [poitouBump_even]
      rw [show -t - u = -(t + u) by ring,
        show t - -u = t + u by ring, poitouBump_even]
    _ = ∫ u : ℝ, f u := hneg
    _ = poitouBumpAutocorrelation t := rfl

theorem poitouBumpAutocorrelation_eq_zero_of_two_le_abs
    {t : ℝ} (ht : 2 ≤ |t|) : poitouBumpAutocorrelation t = 0 := by
  unfold poitouBumpAutocorrelation
  have hfun : (fun u : ℝ ↦ poitouBump u * poitouBump (t - u)) =
      (fun _ : ℝ ↦ 0) := by
    funext u
    by_cases hu : 1 ≤ |u|
    · rw [poitouBump_eq_zero_of_one_le_abs hu]
      simp
    by_cases htu : 1 ≤ |t - u|
    · rw [poitouBump_eq_zero_of_one_le_abs htu]
      simp
    have hu' : |u| < 1 := lt_of_not_ge hu
    have htu' : |t - u| < 1 := lt_of_not_ge htu
    have htriangle : |t| ≤ |u| + |t - u| := by
      calc
        |t| = |u + (t - u)| := by ring
        _ ≤ |u| + |t - u| := by
          simpa only [Real.norm_eq_abs] using norm_add_le u (t - u)
    exfalso
    linarith
  rw [hfun, integral_zero]

theorem poitouBumpAutocorrelation_nonneg (t : ℝ) :
    0 ≤ poitouBumpAutocorrelation t := by
  unfold poitouBumpAutocorrelation
  exact integral_nonneg fun u ↦
    mul_nonneg (poitouBump_nonneg u) (poitouBump_nonneg (t - u))

/-- The Fourier transform of Poitou's squared amplitude is the rescaled bump
autocorrelation. -/
theorem poitouTest_fourier_eq_autocorrelation (w : ℝ) :
    𝓕 poitouTestComplex w =
      (((2 * Real.pi) *
        poitouBumpAutocorrelation ((2 * Real.pi) * w) : ℝ) : ℂ) := by
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hc0 : c ≠ 0 := hc.ne'
  let F : ℝ → ℂ := fun u ↦
    ((poitouBump u * poitouBump (c * w - u) : ℝ) : ℂ)
  have hscale := Measure.integral_comp_mul_left F c
  have hF : (∫ u : ℝ, F u) =
      (poitouBumpAutocorrelation (c * w) : ℂ) := by
    dsimp only [F, poitouBumpAutocorrelation]
    convert (@integral_ofReal ℝ _ volume ℂ _
      (fun u : ℝ ↦ poitouBump u * poitouBump (c * w - u))) using 1
    all_goals try with_reducible_and_instances rfl
  rw [poitouTest_fourier_eq_convolution, MeasureTheory.convolution_mul]
  calc
    (∫ z : ℝ, 𝓕 poitouAmplitudeComplex z *
        𝓕 poitouAmplitudeComplex (w - z)) =
        ∫ z : ℝ, ((c ^ 2 : ℝ) : ℂ) * F (c * z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [poitouAmplitude_fourier_eq_bump,
        poitouAmplitude_fourier_eq_bump]
      dsimp only [F, c, poitouBumpComplex]
      rw [show 2 * Real.pi * (w - z) =
        2 * Real.pi * w - 2 * Real.pi * z by ring]
      push_cast
      ring
    _ = ((c ^ 2 : ℝ) : ℂ) * ∫ z : ℝ, F (c * z) := by
      rw [integral_const_mul]
    _ = ((c ^ 2 : ℝ) : ℂ) *
        (((c⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, F u) := by
      rw [hscale]
      rw [abs_of_pos (inv_pos.mpr hc), Complex.real_smul]
    _ = ((c : ℝ) : ℂ) *
        (poitouBumpAutocorrelation (c * w) : ℂ) := by
      rw [hF]
      push_cast
      field_simp [hc0]
    _ = (((2 * Real.pi) *
        poitouBumpAutocorrelation ((2 * Real.pi) * w) : ℝ) : ℂ) := by
      dsimp only [c]
      push_cast
      ring

theorem poitouTestComplex_fourier_integrable :
    Integrable (𝓕 poitouTestComplex) volume := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hscaled : Integrable
      (fun w : ℝ ↦ poitouBumpAutocorrelation ((2 * Real.pi) * w))
      volume :=
    poitouBumpAutocorrelation_integrable.comp_mul_left' hc
  have hreal : Integrable
      (fun w : ℝ ↦ (2 * Real.pi) *
        poitouBumpAutocorrelation ((2 * Real.pi) * w)) volume :=
    hscaled.const_mul (2 * Real.pi : ℝ)
  have hmajor : Integrable
      (fun w : ℝ ↦ (((2 * Real.pi) *
        poitouBumpAutocorrelation ((2 * Real.pi) * w) : ℝ) : ℂ)) volume :=
    hreal.ofReal
  exact hmajor.congr (Filter.Eventually.of_forall fun w ↦ by
    rw [poitouTest_fourier_eq_autocorrelation])

theorem poitouTest_fourierInv_fourier (x : ℝ) :
    𝓕⁻ (𝓕 poitouTestComplex) x = poitouTestComplex x := by
  exact congrFun
    (poitouTestComplex_continuous.fourierInv_fourier_eq
      poitouTestComplex_integrable poitouTestComplex_fourier_integrable) x

theorem poitouTest_fourier_inversion_integral (x : ℝ) :
    (∫ w : ℝ,
        Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
          𝓕 poitouTestComplex w) = poitouTestComplex x := by
  have h := poitouTest_fourierInv_fourier x
  rw [Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul, RCLike.inner_apply, conj_trivial, mul_assoc,
    mul_comm, mul_left_comm] using h

/-- Fourier inversion in Poitou's angular-frequency normalization. -/
theorem poitouTest_eq_autocorrelation_fourierIntegral (x : ℝ) :
    (∫ t : ℝ,
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          (poitouBumpAutocorrelation t : ℂ)) = poitouTestComplex x := by
  let c : ℝ := 2 * Real.pi
  let a : ℝ := c⁻¹
  let g : ℝ → ℂ := fun w ↦
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 poitouTestComplex w
  let H : ℝ → ℂ := fun t ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
      (poitouBumpAutocorrelation t : ℂ)
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hpoint (t : ℝ) : g (a * t) = ((c : ℝ) : ℂ) * H t := by
    dsimp only [g, H]
    rw [poitouTest_fourier_eq_autocorrelation]
    have hfreq : 2 * Real.pi * (a * t) = t := by
      dsimp only [a, c]
      field_simp [Real.pi_ne_zero]
    rw [hfreq]
    dsimp only [c]
    push_cast
    ring
  have hscale := Measure.integral_comp_mul_left g a
  have hinv : (∫ w : ℝ, g w) = poitouTestComplex x := by
    simpa only [g] using poitouTest_fourier_inversion_integral x
  have hcInv : |a⁻¹| = c := by
    dsimp only [a]
    rw [inv_inv, abs_of_pos hc]
  have hleft : (∫ t : ℝ, g (a * t)) =
      ((c : ℝ) : ℂ) * ∫ t : ℝ, H t := by
    calc
      (∫ t : ℝ, g (a * t)) = ∫ t : ℝ, ((c : ℝ) : ℂ) * H t := by
        apply integral_congr_ae
        filter_upwards with t
        exact hpoint t
      _ = ((c : ℝ) : ℂ) * ∫ t : ℝ, H t := by
        rw [integral_const_mul]
  rw [hleft, hcInv, Complex.real_smul, hinv] at hscale
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  apply (mul_left_cancel₀ hcC)
  simpa only [H] using hscale

/-- Real form of the autocorrelation inversion formula. -/
theorem poitouTest_eq_autocorrelation_cosineIntegral (x : ℝ) :
    poitouTest x =
      ∫ t : ℝ, poitouBumpAutocorrelation t * Real.cos (t * x) := by
  let H : ℝ → ℂ := fun t ↦
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
      (poitouBumpAutocorrelation t : ℂ)
  have hH : Integrable H volume := by
    have hq : Integrable
        (fun t : ℝ ↦ (poitouBumpAutocorrelation t : ℂ)) volume :=
      poitouBumpAutocorrelation_integrable.ofReal
    have hexpMeas : AEStronglyMeasurable
        (fun t : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) volume := by
      fun_prop
    have hexpBound : ∀ᵐ t : ℝ ∂volume,
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
      filter_upwards with t
      rw [Complex.norm_exp]
      norm_num
    have hmul := hq.mul_bdd hexpMeas hexpBound
    exact hmul.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp only [H]
      ring)
  calc
    poitouTest x = (poitouTestComplex x).re := rfl
    _ = (∫ t : ℝ, H t).re := by
      rw [poitouTest_eq_autocorrelation_fourierIntegral x]
    _ = ∫ t : ℝ, (H t).re := (integral_re hH).symm
    _ = ∫ t : ℝ, poitouBumpAutocorrelation t * Real.cos (t * x) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [H]
      rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
      simp
      ring

theorem poitouBumpAutocorrelation_integral :
    (∫ t : ℝ, poitouBumpAutocorrelation t) = 1 := by
  have h := poitouTest_eq_autocorrelation_cosineIntegral 0
  simpa using h.symm

theorem one_sub_poitouTest_eq_autocorrelation_integral (z : ℝ) :
    1 - poitouTest z =
      ∫ t : ℝ, poitouBumpAutocorrelation t *
        (1 - Real.cos (t * z)) := by
  have hcos : Integrable
      (fun t : ℝ ↦ poitouBumpAutocorrelation t * Real.cos (t * z))
      volume := by
    apply poitouBumpAutocorrelation_integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with t
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * z)
  calc
    1 - poitouTest z =
        (∫ t : ℝ, poitouBumpAutocorrelation t) -
          ∫ t : ℝ, poitouBumpAutocorrelation t * Real.cos (t * z) := by
      rw [poitouBumpAutocorrelation_integral,
        poitouTest_eq_autocorrelation_cosineIntegral]
    _ = ∫ t : ℝ, (poitouBumpAutocorrelation t -
        poitouBumpAutocorrelation t * Real.cos (t * z)) := by
      rw [integral_sub poitouBumpAutocorrelation_integrable hcos]
    _ = ∫ t : ℝ, poitouBumpAutocorrelation t *
        (1 - Real.cos (t * z)) := by
      apply integral_congr_ae
      filter_upwards with t
      ring

private theorem poitouExpCos_integrableOn (b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * Real.cos (b * x))
      (Set.Ioi 0) := by
  let a : ℂ := (-1 : ℂ) + (b : ℂ) * Complex.I
  have ha : a.re < 0 := by simp [a]
  have h := integrableOn_exp_mul_complex_Ioi ha 0
  have hre := Complex.reCLM.integrable_comp h
  apply hre.congr
  filter_upwards with x
  change (Complex.exp (a * (x : ℂ))).re = _
  dsimp only [a]
  rw [show (((-1 : ℂ) + (b : ℂ) * Complex.I) * (x : ℂ)) =
      ((-x : ℝ) : ℂ) + ((b * x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.mul_re, Complex.exp_ofReal_re,
    Complex.exp_ofReal_im, Complex.exp_ofReal_mul_I_re]
  simp

/-- Elementary Laplace transform used in Poitou's definition of `L`. -/
theorem poitouExpCos_integral (b : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
        2 * Real.exp (-x) * (1 - Real.cos (b * x))) =
      2 * b ^ 2 / (1 + b ^ 2) := by
  let a : ℂ := (-1 : ℂ) + (b : ℂ) * Complex.I
  have ha : a.re < 0 := by simp [a]
  have hcomplex := integral_exp_mul_complex_Ioi ha 0
  have hintComplex := integrableOn_exp_mul_complex_Ioi ha 0
  have hcos : (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-x) * Real.cos (b * x)) = 1 / (1 + b ^ 2) := by
    have hre := integral_re hintComplex
    have hpoint : ∀ x : ℝ,
        (Complex.exp (a * (x : ℂ))).re =
          Real.exp (-x) * Real.cos (b * x) := by
      intro x
      dsimp only [a]
      rw [show (((-1 : ℂ) + (b : ℂ) * Complex.I) * (x : ℂ)) =
          ((-x : ℝ) : ℂ) + ((b * x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      rw [Complex.exp_add, Complex.mul_re, Complex.exp_ofReal_re,
        Complex.exp_ofReal_im, Complex.exp_ofReal_mul_I_re]
      simp
    calc
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * Real.cos (b * x)) =
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (a * (x : ℂ))).re := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        exact (hpoint x).symm
      _ = (∫ x in Set.Ioi (0 : ℝ),
          Complex.exp (a * (x : ℂ))).re := hre
      _ = 1 / (1 + b ^ 2) := by
        rw [hcomplex]
        dsimp only [a]
        simp [Complex.div_re, Complex.normSq_apply]
        field_simp
  have hexp := integral_exp_neg_Ioi_zero
  have hiExp := integrableOn_exp_neg_Ioi 0
  have hiCos := poitouExpCos_integrableOn b
  calc
    (∫ x in Set.Ioi (0 : ℝ),
        2 * Real.exp (-x) * (1 - Real.cos (b * x))) =
        2 * ((∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) -
          ∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-x) * Real.cos (b * x)) := by
      rw [← integral_sub hiExp hiCos, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ = 2 * b ^ 2 / (1 + b ^ 2) := by
      rw [hexp, hcos]
      have hden : 0 < 1 + b ^ 2 := by positivity
      field_simp
      ring

def poitouAutocorrelationLaplaceIntegrand (y t : ℝ) : ℝ :=
  4 * poitouAutocorrelationPolynomial t * y * t ^ 2 / (1 + y * t ^ 2)

private def poitouAutocorrelationLaplacePrimitive (y t : ℝ) : ℝ :=
  (-1 / 80) * t ^ 6 +
  (3 / 8 + 3 / (160 * y)) * t ^ 4 +
  (-1) * t ^ 3 +
  (-(3 / (4 * y) + 3 / (80 * y ^ 2))) * t ^ 2 +
  (12 / 5 + 3 / y) * t +
  (3 / (4 * y ^ 2) + 3 / (80 * y ^ 3)) *
    Real.log (1 + y * t ^ 2) +
  (-(12 / 5 + 3 / y) / Real.sqrt y) *
    Real.arctan (Real.sqrt y * t)

private theorem poitouLogTerm_hasDerivAt {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.log (1 + y * u ^ 2))
      (2 * y * t / (1 + y * t ^ 2)) t := by
  have harg : HasDerivAt (fun u : ℝ ↦ 1 + y * u ^ 2)
      (y * (2 * t)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul y).const_add 1 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try funext u
    all_goals try simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    all_goals try ring
  have hne : 1 + y * t ^ 2 ≠ 0 := by positivity
  convert harg.log hne using 1 <;> field_simp <;> ring

private theorem poitouArctanTerm_hasDerivAt {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan (Real.sqrt y * u))
      (Real.sqrt y / (1 + y * t ^ 2)) t := by
  have hs : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  have harg : HasDerivAt (fun u : ℝ ↦ Real.sqrt y * u)
      (Real.sqrt y) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (Real.sqrt y)
  convert harg.arctan using 1
  rw [show (Real.sqrt y * t) ^ 2 = y * t ^ 2 by rw [mul_pow, hs]]
  ring

private theorem poitouAutocorrelationLaplacePrimitive_hasDerivAt {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (poitouAutocorrelationLaplacePrimitive y) (poitouAutocorrelationLaplaceIntegrand y t) t := by
  have hy0 : y ≠ 0 := hy.ne'
  have hlog : HasDerivAt (fun u : ℝ ↦ Real.log (1 + y * u ^ 2))
      (2 * y * t / (1 + y * t ^ 2)) t := by
    have harg : HasDerivAt (fun u : ℝ ↦ 1 + y * u ^ 2)
        (y * (2 * t)) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul y).const_add 1 using 1
      all_goals try with_reducible_and_instances rfl
      all_goals try funext u
      all_goals try simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one, mul_one]
    have hne : 1 + y * t ^ 2 ≠ 0 := by positivity
    convert harg.log hne using 1 <;> field_simp <;> ring
  have hs : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  have hatan : HasDerivAt (fun u : ℝ ↦ Real.arctan (Real.sqrt y * u))
      (Real.sqrt y / (1 + y * t ^ 2)) t := by
    have harg : HasDerivAt (fun u : ℝ ↦ Real.sqrt y * u)
        (Real.sqrt y) t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul (Real.sqrt y)
    convert harg.arctan using 1
    rw [show (Real.sqrt y * t) ^ 2 = y * t ^ 2 by rw [mul_pow, hs]]
    ring
  have h6 := ((hasDerivAt_id t).pow 6).const_mul (-1 / 80 : ℝ)
  have h4 := ((hasDerivAt_id t).pow 4).const_mul
    (3 / 8 + 3 / (160 * y) : ℝ)
  have h3 := ((hasDerivAt_id t).pow 3).const_mul (-1 : ℝ)
  have h2 := ((hasDerivAt_id t).pow 2).const_mul
    (-(3 / (4 * y) + 3 / (80 * y ^ 2)) : ℝ)
  have h1 := (hasDerivAt_id t).const_mul (12 / 5 + 3 / y : ℝ)
  have hl := hlog.const_mul
    (3 / (4 * y ^ 2) + 3 / (80 * y ^ 3) : ℝ)
  have ha := hatan.const_mul
    (-(12 / 5 + 3 / y) / Real.sqrt y : ℝ)
  have hsum := (((((h6.add h4).add h3).add h2).add h1).add hl).add ha
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try funext u
  all_goals try simp only [poitouAutocorrelationLaplacePrimitive, Pi.add_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  all_goals try unfold poitouAutocorrelationLaplaceIntegrand poitouAutocorrelationPolynomial
  all_goals try rw [hs]
  all_goals try field_simp [hy0]
  all_goals try ring

theorem poitouLClosed_eq_autocorrelation_integral {y : ℝ} (hy : 0 < y) :
    (∫ t in (0 : ℝ)..2, poitouAutocorrelationLaplaceIntegrand y t) =
      TraceEuclidean.PoitouDegreeEleven.poitouLClosed y := by
  have hcont : Continuous (poitouAutocorrelationLaplaceIntegrand y) := by
    unfold poitouAutocorrelationLaplaceIntegrand poitouAutocorrelationPolynomial
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ poitouAutocorrelationLaplacePrimitive_hasDerivAt hy t) (hcont.intervalIntegrable 0 2)]
  unfold poitouAutocorrelationLaplacePrimitive TraceEuclidean.PoitouDegreeEleven.poitouLClosed
  simp
  field_simp [hy.ne']
  ring

/-- Integral definition of Poitou's auxiliary `L` function. -/
def poitouBaseLaplaceIntegral (y : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    2 * Real.exp (-x) * (1 - poitouScaledTest y x)

private theorem poitouLaplaceJoint_integrable {y : ℝ} (hy : 0 < y) :
    Integrable
      (fun z : ℝ × ℝ ↦
        2 * Real.exp (-z.1) * poitouBumpAutocorrelation z.2 *
          (1 - Real.cos (z.2 * Real.sqrt y * z.1)))
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hx : Integrable (fun x : ℝ ↦ 4 * Real.exp (-x))
      (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul 4
  have hmajor := hx.mul_prod poitouBumpAutocorrelation_integrable
  have hmultMeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦
        (1 - Real.cos (z.2 * Real.sqrt y * z.1)) / 2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    fun_prop
  have hmultBound : ∀ᵐ z : ℝ × ℝ
      ∂((volume.restrict (Set.Ioi 0)).prod volume),
      ‖(1 - Real.cos (z.2 * Real.sqrt y * z.1)) / 2‖ ≤ 1 := by
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hcos2 : 1 - Real.cos (z.2 * Real.sqrt y * z.1) ≤ 2 := by
        linarith [Real.neg_one_le_cos (z.2 * Real.sqrt y * z.1)]
      linarith
    · have hcos0 : 0 ≤ 1 - Real.cos (z.2 * Real.sqrt y * z.1) := by
        linarith [Real.cos_le_one (z.2 * Real.sqrt y * z.1)]
      positivity
  have hproduct := hmajor.mul_bdd hmultMeas hmultBound
  convert hproduct using 1
  funext z
  ring

/-- The source Laplace integral equals the rational-logarithmic-arctangent
closed form used by the numerical certificate. -/
theorem poitouLClosed_eq_baseLaplaceIntegral {y : ℝ} (hy : 0 < y) :
    poitouBaseLaplaceIntegral y = poitouLClosed y := by
  let a : ℝ := Real.sqrt y
  have ha : 0 < a := Real.sqrt_pos.2 hy
  have haSq : a ^ 2 = y := Real.sq_sqrt hy.le
  let J : ℝ × ℝ → ℝ := fun z ↦
    2 * Real.exp (-z.1) * poitouBumpAutocorrelation z.2 *
      (1 - Real.cos (z.2 * a * z.1))
  have hJ : Integrable J ((volume.restrict (Set.Ioi 0)).prod volume) := by
    simpa only [J, a] using poitouLaplaceJoint_integrable hy
  have hsource (x : ℝ) :
      1 - poitouScaledTest y x =
        ∫ t : ℝ, poitouBumpAutocorrelation t *
          (1 - Real.cos (t * a * x)) := by
    rw [poitouScaledTest,
      one_sub_poitouTest_eq_autocorrelation_integral]
    dsimp only [a]
    apply integral_congr_ae
    filter_upwards with t
    congr 3
    ring
  calc
    poitouBaseLaplaceIntegral y =
        ∫ x in Set.Ioi (0 : ℝ), ∫ t : ℝ, J (x, t) := by
      unfold poitouBaseLaplaceIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change 2 * Real.exp (-x) * (1 - poitouScaledTest y x) =
        ∫ t : ℝ, J (x, t)
      rw [hsource x, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [J]
      ring
    _ = ∫ t : ℝ, ∫ x in Set.Ioi (0 : ℝ), J (x, t) :=
      integral_integral_swap hJ
    _ = ∫ t : ℝ, poitouBumpAutocorrelation t *
        (2 * (t * a) ^ 2 / (1 + (t * a) ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with t
      calc
        (∫ x in Set.Ioi (0 : ℝ), J (x, t)) =
            poitouBumpAutocorrelation t *
              ∫ x in Set.Ioi (0 : ℝ),
                2 * Real.exp (-x) * (1 - Real.cos ((t * a) * x)) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          dsimp only [J]
          ring
        _ = poitouBumpAutocorrelation t *
            (2 * (t * a) ^ 2 / (1 + (t * a) ^ 2)) := by
          rw [poitouExpCos_integral]
    _ = ∫ t : ℝ, poitouBumpAutocorrelation t *
        (2 * y * t ^ 2 / (1 + y * t ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [mul_pow, haSq]
      ring
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ),
        poitouBumpAutocorrelation t *
          (2 * y * t ^ 2 / (1 + y * t ^ 2)) := by
      let f : ℝ → ℝ := fun t ↦ poitouBumpAutocorrelation t *
        (2 * y * t ^ 2 / (1 + y * t ^ 2))
      have heven (t : ℝ) : f |t| = f t := by
        dsimp only [f]
        rcases le_total 0 t with ht | ht
        · rw [abs_of_nonneg ht]
        · rw [abs_of_nonpos ht, poitouBumpAutocorrelation_even]
          simp only [neg_sq]
      calc
        (∫ t : ℝ, poitouBumpAutocorrelation t *
            (2 * y * t ^ 2 / (1 + y * t ^ 2))) =
            ∫ t : ℝ, f |t| := by
          apply integral_congr_ae
          filter_upwards with t
          exact (heven t).symm
        _ = 2 * ∫ t in Set.Ioi (0 : ℝ), f t := integral_comp_abs
        _ = _ := rfl
    _ = 2 * ∫ t in Set.Ioc (0 : ℝ) 2,
        poitouBumpAutocorrelation t *
          (2 * y * t ^ 2 / (1 + y * t ^ 2)) := by
      congr 1
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (by intro t ht; exact ht.1)
      intro t ht
      have ht2 : 2 ≤ |t| := by
        rw [abs_of_pos ht.1]
        have hnotle : ¬ t ≤ 2 := by
          intro hle
          exact ht.2 ⟨ht.1, hle⟩
        exact (lt_of_not_ge hnotle).le
      rw [poitouBumpAutocorrelation_eq_zero_of_two_le_abs ht2]
      simp
    _ = ∫ t in (0 : ℝ)..2, poitouAutocorrelationLaplaceIntegrand y t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change 2 * (poitouBumpAutocorrelation t *
        (2 * y * t ^ 2 / (1 + y * t ^ 2))) =
        poitouAutocorrelationLaplaceIntegrand y t
      rw [poitouBumpAutocorrelation_eq_polynomial ht.1.le ht.2]
      unfold poitouAutocorrelationLaplaceIntegrand
      ring
    _ = poitouLClosed y := poitouLClosed_eq_autocorrelation_integral hy


end

end TraceEuclidean.PoitouKernel
