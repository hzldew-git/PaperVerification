import DedekindZeta.LogDeriv
import TraceEuclidean.OdlyzkoArchimedeanBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Prime-power transform in the Odlyzko explicit formula

This file matches the prime-power Euler terms with the source-normalized
finite prime correction.  The exponent stored by `primePowerLogTerm` is
`m + 1`; this is the positive exponent used by Odlyzko's sum.
-/

namespace TraceEuclidean

noncomputable section

open Complex FourierTransform IsDedekindDomain MeasureTheory
open scoped NumberField RealInnerProductSpace

variable {K : Type*} [Field K] [NumberField K]

/-- On every fixed vertical line, the compactly supported `C⁴` source kernel
gives fourth-power decay of its transform.  Unlike the zero-sum estimate, no
restriction to the critical strip is needed here. -/
theorem odlyzkoPhi_vertical_exists_fourthPowerBound (σ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
      ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D / (1 + |t|) ^ 4 := by
  let a : ℝ := σ - 1 / 2
  let f : ℝ → ℂ := odlyzkoTiltedF4 a
  let M₀ : ℝ := ∫ x : ℝ, ‖f x‖
  let M₄ : ℝ := ∫ x : ℝ, ‖iteratedDeriv 4 f x‖
  have hSmooth : ContDiff ℝ 4 f := by
    simpa only [f] using odlyzkoTiltedF4_contDiff_four a
  have hInt : ∀ k : ℕ, (k : ℕ∞) ≤ 4 →
      Integrable (iteratedDeriv k f) volume := by
    intro k hk
    simpa only [f] using
      odlyzkoTiltedF4_iteratedDeriv_integrable_of_contDiff a
        (odlyzkoTiltedF4_contDiff_four a) k hk
  have hM₀ : 0 ≤ M₀ := integral_nonneg fun x ↦ norm_nonneg (f x)
  have hM₄ : 0 ≤ M₄ := integral_nonneg fun x ↦ norm_nonneg (iteratedDeriv 4 f x)
  refine ⟨8 * (M₀ + M₄), by positivity, ?_⟩
  intro t
  let w : ℝ := -t / (2 * Real.pi)
  have hPhi :
      odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) = 𝓕 f w := by
    have hre :
        (((σ : ℂ) + (t : ℂ) * Complex.I).re - 1 / 2) = a := by
      norm_num [a, Complex.mul_re]
    have him :
        -((σ : ℂ) + (t : ℂ) * Complex.I).im / (2 * Real.pi) = w := by
      norm_num [w, Complex.mul_im]
    simpa only [hre, him, f] using
      odlyzkoPhi_eq_fourier ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hZero :
      ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M₀ := by
    rw [hPhi]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) f w
  have hFourth :
      |t| ^ 4 * ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M₄ := by
    have h := fourier_fourth_frequency_bound f hSmooth hInt w
    rw [odlyzko_fourth_frequency_normalization t, ← hPhi] at h
    exact h
  have hAbs : 0 ≤ |t| := abs_nonneg _
  have hPow : (1 + |t|) ^ 4 ≤ 8 * (1 + |t| ^ 4) := by
    have hFactor : 0 ≤ (|t| - 1) ^ 2 *
        (7 * |t| ^ 2 + 10 * |t| + 7) := by positivity
    nlinarith
  have hProduct :
      (1 + |t|) ^ 4 *
          ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        8 * (M₀ + M₄) := by
    calc
      _ ≤ (8 * (1 + |t| ^ 4)) *
          ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ = 8 * (‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
          |t| ^ 4 *
            ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by ring
      _ ≤ 8 * (M₀ + M₄) := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).2
  simpa only [mul_comm] using hProduct

/-- The exact Odlyzko transform is integrable on every fixed vertical line. -/
theorem odlyzkoPhi_vertical_integrable (σ : ℝ) :
    Integrable
      (fun t : ℝ ↦ odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
  obtain ⟨D, hD, hDecay⟩ :=
    odlyzkoPhi_vertical_exists_fourthPowerBound σ
  apply (odlyzkoCriticalMajorant_integrable D).mono'
  · exact (odlyzkoPhi_differentiable.continuous.comp
      (by fun_prop : Continuous
        (fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards with t
    exact hDecay t

/-- The Fourier transform of every fixed exponential tilt of the source
kernel is integrable. -/
theorem odlyzkoTiltedF4_fourier_integrable (a : ℝ) :
    Integrable (𝓕 (odlyzkoTiltedF4 a)) volume := by
  let σ : ℝ := a + 1 / 2
  have hscaled := (odlyzkoPhi_vertical_integrable σ).comp_mul_left'
    (show (-2 * Real.pi : ℝ) ≠ 0 by positivity)
  apply hscaled.congr
  filter_upwards with w
  have hre :
      (((σ : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).re -
          1 / 2) = a := by
    norm_num [σ, Complex.mul_re]
  have him :
      -((σ : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).im /
          (2 * Real.pi) = w := by
    norm_num [Complex.mul_im]
  simpa only [hre, him] using
    odlyzkoPhi_eq_fourier
      ((σ : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I)

/-- Fourier inversion is available for every fixed exponential tilt. -/
theorem odlyzkoTiltedF4_fourierInv_fourier (a x : ℝ) :
    𝓕⁻ (𝓕 (odlyzkoTiltedF4 a)) x = odlyzkoTiltedF4 a x := by
  exact congrFun
    ((odlyzkoTiltedF4_continuous a).fourierInv_fourier_eq
      (odlyzkoTiltedF4_integrable a)
      (odlyzkoTiltedF4_fourier_integrable a)) x

/-- Fourier inversion for a fixed tilt, written as an ordinary complex
integral. -/
theorem odlyzkoTiltedF4_fourier_inversion_integral (a x : ℝ) :
    (∫ w : ℝ,
        Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
          𝓕 (odlyzkoTiltedF4 a) w) =
      odlyzkoTiltedF4 a x := by
  have h := odlyzkoTiltedF4_fourierInv_fourier a x
  rw [Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul, RCLike.inner_apply, conj_trivial, mul_assoc,
    mul_comm, mul_left_comm] using h

/-- Multiplication by a fixed Fourier phase preserves vertical-line
integrability. -/
theorem odlyzkoPhi_vertical_phase_integrable (σ x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hprod : Integrable
      (fun t : ℝ ↦
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I)) volume := by
    apply (odlyzkoPhi_vertical_integrable σ).mul_bdd (c := 1)
    · exact (by fun_prop : Continuous
        (fun t : ℝ ↦
          Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
    · filter_upwards with t
      rw [Complex.norm_exp]
      norm_num
  exact hprod.congr (Filter.Eventually.of_forall fun t ↦ by ring)

/-- Fourier inversion in the source's vertical-line parameter.  The real
exponential tilt on the right is exactly the shift from `1/2` to `σ`. -/
theorem odlyzkoPhi_vertical_inversion_integral (σ x : ℝ) :
    (∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (2 * Real.pi : ℝ) • odlyzkoTiltedF4 (σ - 1 / 2) x := by
  let a : ℝ := -1 / (2 * Real.pi)
  let g : ℝ → ℂ := fun w ↦
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (odlyzkoTiltedF4 (σ - 1 / 2)) w
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hpoint (t : ℝ) :
      Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) =
        g (a * t) := by
    have hat : a * t = -t / (2 * Real.pi) := by
      dsimp [a]
      field_simp [Real.pi_ne_zero]
    have hre :
        (((σ : ℂ) + (t : ℂ) * Complex.I).re - 1 / 2) = σ - 1 / 2 := by
      norm_num [Complex.mul_re]
    have him :
        -((σ : ℂ) + (t : ℂ) * Complex.I).im / (2 * Real.pi) =
          -t / (2 * Real.pi) := by
      norm_num [Complex.mul_im]
    dsimp [g]
    rw [hat, ← show
      odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) =
        𝓕 (odlyzkoTiltedF4 (σ - 1 / 2)) (-t / (2 * Real.pi)) by
          simpa only [hre, him] using
            odlyzkoPhi_eq_fourier
              ((σ : ℂ) + (t : ℂ) * Complex.I)]
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
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ, g (a * t) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = |a⁻¹| • ∫ w : ℝ, g w := Measure.integral_comp_mul_left g a
    _ = (2 * Real.pi : ℝ) •
        odlyzkoTiltedF4 (σ - 1 / 2) x := by
      rw [habs]
      change (2 * Real.pi : ℝ) •
          (∫ w : ℝ,
            Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
              𝓕 (odlyzkoTiltedF4 (σ - 1 / 2)) w) = _
      rw [odlyzkoTiltedF4_fourier_inversion_integral]

private theorem odlyzkoPrimeTransform_absNorm_one_lt
    (P : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm P.asIdeal := by
  by_contra! h
  apply Ideal.IsPrime.ne_top P.isPrime
  rw [← Ideal.absNorm_eq_one_iff]
  have hpos : 0 < Ideal.absNorm P.asIdeal := by
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  omega

/-- A prime-power Euler term on an arbitrary vertical line splits into a
constant real amplitude and the Fourier phase used by the source kernel. -/
theorem odlyzkoPrimePowerLogTerm_vertical_eq
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (σ t : ℝ) :
    DedekindZeta.primePowerLogTerm K P m
        ((σ : ℂ) + (t : ℂ) * Complex.I) =
      ((Real.log (Ideal.absNorm P.asIdeal : ℝ) *
          Real.exp (-σ *
            Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1))) : ℝ) : ℂ) *
        Complex.exp
          (((-t * Real.log
            ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1)) : ℝ) : ℂ) *
              Complex.I) := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  have hqNat : 1 < Ideal.absNorm P.asIdeal :=
    odlyzkoPrimeTransform_absNorm_one_lt P
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hpow :
      ((q : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) ^ n =
        Complex.exp
          (Complex.log (q : ℂ) *
            ((n : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I)))) := by
    rw [← Complex.cpow_nat_mul, Complex.cpow_def_of_ne_zero hqC]
  have hlog : Complex.log (q : ℂ) = (Real.log q : ℂ) :=
    (Complex.ofReal_log hq.le).symm
  have hx : x = (n : ℝ) * Real.log q := by
    dsimp [x]
    rw [Real.log_pow]
  have hexponent :
      Complex.log (q : ℂ) *
          ((n : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
        ((-σ * x : ℝ) : ℂ) + ((-t * x : ℝ) : ℂ) * Complex.I := by
    rw [hlog, hx]
    push_cast
    ring
  unfold DedekindZeta.primePowerLogTerm DedekindZeta.primeEulerParameter
  change Complex.log (q : ℂ) *
      ((q : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) ^ n = _
  rw [hpow, hexponent, Complex.exp_add, hlog]
  rw [show Complex.exp ((-σ * x : ℝ) : ℂ) =
      (Real.exp (-σ * x) : ℂ) by exact (Complex.ofReal_exp _).symm]
  dsimp [q, n, x]
  push_cast
  ring

/-- One vertical-line prime-power integrand is absolutely integrable. -/
theorem odlyzkoPhi_mul_primePowerLogTerm_integrable
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (σ : ℝ) :
    Integrable
      (fun t : ℝ ↦
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            ((σ : ℂ) + (t : ℂ) * Complex.I)) volume := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℂ :=
    (Real.log q * Real.exp (-σ * x) : ℝ)
  have hphase := odlyzkoPhi_vertical_phase_integrable σ x
  apply (hphase.const_mul c).congr
  filter_upwards with t
  rw [odlyzkoPrimePowerLogTerm_vertical_eq]
  dsimp [q, n, x, c]
  ring

/-- The right-half-plane transform of one prime-power Euler term is exactly
half of the corresponding source correction term. -/
theorem odlyzkoPhi_mul_primePowerLogTerm_integral
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (σ : ℝ) :
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ((Real.pi * odlyzkoPrimeTerm P (m + 1) : ℝ) : ℂ) := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℂ := (Real.log q * Real.exp (-σ * x) : ℝ)
  have hqNat : 1 < Ideal.absNorm P.asIdeal :=
    odlyzkoPrimeTransform_absNorm_one_lt P
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hpoint (t : ℝ) :
      odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            ((σ : ℂ) + (t : ℂ) * Complex.I) =
        c * (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [odlyzkoPrimePowerLogTerm_vertical_eq]
    dsimp [q, n, x, c]
    ring
  have hexpHalf :
      Real.exp (-(x / 2)) = (q ^ ((n : ℝ) / 2))⁻¹ := by
    rw [show x = (n : ℝ) * Real.log q by
      dsimp [x]
      rw [Real.log_pow]]
    rw [Real.rpow_def_of_pos hq, Real.exp_neg]
    congr 1
    ring
  calc
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ, c *
          (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
            odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = c * ∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      rw [integral_const_mul]
    _ = c * ((2 * Real.pi : ℝ) •
        odlyzkoTiltedF4 (σ - 1 / 2) x) := by
      rw [odlyzkoPhi_vertical_inversion_integral]
    _ = ((Real.pi * odlyzkoPrimeTerm P (m + 1) : ℝ) : ℂ) := by
      unfold odlyzkoTiltedF4 odlyzkoPrimeTerm
      have hreal :
          Real.log q * Real.exp (-σ * x) *
              (2 * Real.pi *
                (Real.exp ((σ - 1 / 2) * x) * odlyzkoF4 x)) =
            Real.pi *
              (2 * Real.log q * odlyzkoF4 x / q ^ ((n : ℝ) / 2)) := by
        calc
          _ = 2 * Real.pi * Real.log q * odlyzkoF4 x *
              (Real.exp (-σ * x) * Real.exp ((σ - 1 / 2) * x)) := by ring
          _ = 2 * Real.pi * Real.log q * odlyzkoF4 x *
              Real.exp (-σ * x + (σ - 1 / 2) * x) := by
                rw [Real.exp_add]
          _ = 2 * Real.pi * Real.log q * odlyzkoF4 x *
              Real.exp (-(x / 2)) := by
                rw [show -σ * x + (σ - 1 / 2) * x = -(x / 2) by ring]
          _ = _ := by
            rw [hexpHalf, div_eq_mul_inv]
            ring
      have hcast := congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
      simpa [c, q, n, x, Algebra.smul_def] using hcast

/-- The nonzero prime ideals of a number field form a countable type.  The
finite norm balls provide the required exhaustion. -/
theorem odlyzkoPrimePlaces_countable
    (K : Type*) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  apply Set.countable_univ_iff.mp
  have huniv :
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) =
        ⋃ N : ℕ,
          {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ N} := by
    ext P
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm P.asIdeal, le_rfl⟩
  rw [huniv]
  exact Set.countable_iUnion fun N ↦
    (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
      (R := 𝓞 K) N).countable

/-- Absolute convergence on `Re s > 1` justifies exchanging the complete
prime-power sum with the vertical integral.  The result is the full compactly
supported Odlyzko prime correction. -/
theorem odlyzkoPhi_mul_primePowerLogTerm_tsum_integral
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              ((σ : ℂ) + (t : ℂ) * Complex.I))) =
      ((Real.pi * odlyzkoPrimeCorrection K : ℝ) : ℂ) := by
  letI : Countable (HeightOneSpectrum (𝓞 K)) :=
    odlyzkoPrimePlaces_countable K
  let F : (HeightOneSpectrum (𝓞 K) × ℕ) → ℝ → ℂ := fun p t ↦
    odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
      DedekindZeta.primePowerLogTerm K p.1 p.2
        ((σ : ℂ) + (t : ℂ) * Complex.I)
  let C : ℝ :=
    ∫ t : ℝ, ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖
  have hFint (p : HeightOneSpectrum (𝓞 K) × ℕ) :
      Integrable (F p) volume := by
    simpa only [F] using
      odlyzkoPhi_mul_primePowerLogTerm_integrable p.1 p.2 σ
  have hnormConst (p : HeightOneSpectrum (𝓞 K) × ℕ) (t : ℝ) :
      ‖DedekindZeta.primePowerLogTerm K p.1 p.2
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖DedekindZeta.primePowerLogTerm K p.1 p.2 (σ : ℂ)‖ := by
    rw [DedekindZeta.norm_primePowerLogTerm,
      DedekindZeta.norm_primePowerLogTerm]
    norm_num [Complex.mul_re]
  have hFnorm (p : HeightOneSpectrum (𝓞 K) × ℕ) :
      (∫ t : ℝ, ‖F p t‖) =
        ‖DedekindZeta.primePowerLogTerm K p.1 p.2 (σ : ℂ)‖ * C := by
    dsimp only [F, C]
    simp_rw [norm_mul, hnormConst p]
    calc
      (∫ t : ℝ, ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖DedekindZeta.primePowerLogTerm K p.1 p.2 (σ : ℂ)‖) =
          ∫ t : ℝ,
            ‖DedekindZeta.primePowerLogTerm K p.1 p.2 (σ : ℂ)‖ *
              ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = ‖DedekindZeta.primePowerLogTerm K p.1 p.2 (σ : ℂ)‖ *
          ∫ t : ℝ,
            ‖odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [integral_const_mul]
  have hsigmaComplex : 1 < ((σ : ℂ).re) := by simpa using hσ
  have habs :=
    DedekindZeta.summable_norm_primePowerLogTerm K hsigmaComplex
  have hFsum : Summable (fun p : HeightOneSpectrum (𝓞 K) × ℕ ↦
      ∫ t : ℝ, ‖F p t‖) := by
    exact (habs.mul_right C).congr fun p ↦ (hFnorm p).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    hFint hFsum
  calc
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              ((σ : ℂ) + (t : ℂ) * Complex.I))) =
        ∫ t : ℝ, ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, F p t := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [F]
      rw [← tsum_mul_left]
    _ = ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
        ∫ t : ℝ, F p t := hswap.symm
    _ = ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
        ((Real.pi * odlyzkoPrimeTerm p.1 (p.2 + 1) : ℝ) : ℂ) := by
      apply tsum_congr
      intro p
      simpa only [F] using
        odlyzkoPhi_mul_primePowerLogTerm_integral p.1 p.2 σ
    _ = ((Real.pi * odlyzkoPrimeCorrection K : ℝ) : ℂ) := by
      rw [show (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
          ((Real.pi * odlyzkoPrimeTerm p.1 (p.2 + 1) : ℝ) : ℂ)) =
          (Real.pi : ℂ) *
            ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
              (odlyzkoPrimeTerm p.1 (p.2 + 1) : ℂ) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro p
        norm_num]
      rw [← Complex.ofReal_tsum]
      unfold odlyzkoPrimeCorrection
      norm_num

/-- On every line `Re s = σ > 1`, the transformed logarithmic derivative of
the actual Dedekind zeta function is minus the complete Odlyzko prime
correction, with the exact factor `π` dictated by the Fourier normalization. -/
theorem odlyzkoPhi_mul_logDeriv_dedekindZeta_integral
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          logDeriv (NumberField.dedekindZeta K)
            ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      -((Real.pi * odlyzkoPrimeCorrection K : ℝ) : ℂ) := by
  letI : Countable (HeightOneSpectrum (𝓞 K)) :=
    odlyzkoPrimePlaces_countable K
  calc
    (∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          logDeriv (NumberField.dedekindZeta K)
            ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ,
          -(odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
            (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
              DedekindZeta.primePowerLogTerm K p.1 p.2
                ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards with t
      have hline :
          1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
        norm_num [Complex.mul_re]
        exact hσ
      rw [DedekindZeta.LogDeriv.logDeriv_dedekindZeta_eq_neg_tsum_primePowers
        K hline]
      ring
    _ = -(∫ t : ℝ,
        odlyzkoPhi ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      rw [integral_neg]
    _ = -((Real.pi * odlyzkoPrimeCorrection K : ℝ) : ℂ) := by
      rw [odlyzkoPhi_mul_primePowerLogTerm_tsum_integral K σ hσ]

/-- On the critical line, the real part of one prime-power Euler term is the
cosine kernel with the source's square-root norm denominator. -/
theorem odlyzkoPrimePowerLogTerm_critical_re
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (t : ℝ) :
    (DedekindZeta.primePowerLogTerm K P m
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re =
      Real.log (Ideal.absNorm P.asIdeal : ℝ) /
          (Ideal.absNorm P.asIdeal : ℝ) ^ (((m + 1 : ℕ) : ℝ) / 2) *
        Real.cos (t * Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1))) := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  have hqNat : 1 < Ideal.absNorm P.asIdeal :=
    odlyzkoPrimeTransform_absNorm_one_lt P
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hpow :
      ((q : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) ^ n =
        Complex.exp
          (Complex.log (q : ℂ) *
            ((n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)))) := by
    rw [← Complex.cpow_nat_mul, Complex.cpow_def_of_ne_zero hqC]
  have hlog : Complex.log (q : ℂ) = (Real.log q : ℂ) :=
    (Complex.ofReal_log hq.le).symm
  have hexpRe :
      (Complex.exp
        (Complex.log (q : ℂ) *
          ((n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))))).re =
        (q ^ ((n : ℝ) / 2))⁻¹ * Real.cos (t * Real.log (q ^ n)) := by
    rw [Complex.exp_re, hlog]
    have hreal :
        (((Real.log q : ℂ) *
          ((n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)))).re) =
            -((n : ℝ) * Real.log q / 2) := by
      norm_num [Complex.mul_re]
      ring
    have himag :
        (((Real.log q : ℂ) *
          ((n : ℂ) * (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)))).im) =
            -((n : ℝ) * t * Real.log q) := by
      norm_num [Complex.mul_im]
      ring
    rw [hreal, himag, Real.cos_neg, Real.log_pow]
    have hrpow :
        Real.exp (-((n : ℝ) * Real.log q / 2)) =
          (q ^ ((n : ℝ) / 2))⁻¹ := by
      rw [Real.rpow_def_of_pos hq, Real.exp_neg]
      congr 1
      ring
    rw [hrpow]
    congr 2
    ring
  unfold DedekindZeta.primePowerLogTerm DedekindZeta.primeEulerParameter
  change
    (Complex.log (q : ℂ) *
      ((q : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) ^ n).re = _
  rw [hpow, Complex.mul_re, hexpRe, hlog, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  dsimp [q, n]
  rw [div_eq_mul_inv]
  ring

/-- The two conjugate critical-line Euler terms attached to one prime power. -/
def odlyzkoPrimePowerCriticalBracket
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (t : ℝ) : ℝ :=
  (DedekindZeta.primePowerLogTerm K P m
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
    DedekindZeta.primePowerLogTerm K P m
      ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re

/-- The conjugate critical-line bracket is twice the source cosine kernel. -/
theorem odlyzkoPrimePowerCriticalBracket_eq
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) (t : ℝ) :
    odlyzkoPrimePowerCriticalBracket P m t =
      2 * (Real.log (Ideal.absNorm P.asIdeal : ℝ) /
          (Ideal.absNorm P.asIdeal : ℝ) ^ (((m + 1 : ℕ) : ℝ) / 2)) *
        Real.cos (t * Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1))) := by
  have hminus :
      (1 / 2 : ℂ) - (t : ℂ) * Complex.I =
        (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold odlyzkoPrimePowerCriticalBracket
  rw [Complex.add_re, odlyzkoPrimePowerLogTerm_critical_re,
    hminus, odlyzkoPrimePowerLogTerm_critical_re]
  rw [show (-t) * Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1)) =
      -(t * Real.log ((Ideal.absNorm P.asIdeal : ℝ) ^ (m + 1))) by ring,
    Real.cos_neg]
  ring

/-- A single conjugate prime-power bracket is absolutely integrable against
the critical transform. -/
theorem odlyzkoCritical_mul_primePowerBracket_integrable
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Integrable
      (fun t : ℝ ↦ odlyzkoCriticalReal t *
        odlyzkoPrimePowerCriticalBracket P m t) volume := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℝ := 2 * (Real.log q / q ^ ((n : ℝ) / 2))
  have hcos : Integrable
      (fun t : ℝ ↦ odlyzkoCriticalReal t * Real.cos (t * x)) volume := by
    apply odlyzkoCriticalReal_integrable.mul_bdd (c := 1)
    · exact (Real.continuous_cos.comp
        (continuous_id.mul continuous_const)).aestronglyMeasurable
    · filter_upwards with t
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)
  apply (hcos.const_mul c).congr
  filter_upwards with t
  rw [odlyzkoPrimePowerCriticalBracket_eq]
  dsimp [q, n, x, c]
  ring

/-- The exact Fourier pairing of one conjugate prime-power bracket is the
corresponding summand in Odlyzko's source correction. -/
theorem odlyzkoPrimePowerCriticalBracket_integral
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    (∫ t : ℝ, odlyzkoCriticalReal t *
      odlyzkoPrimePowerCriticalBracket P m t) =
        2 * Real.pi * odlyzkoPrimeTerm P (m + 1) := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℝ := 2 * (Real.log q / q ^ ((n : ℝ) / 2))
  have hpoint (t : ℝ) :
      odlyzkoCriticalReal t *
          odlyzkoPrimePowerCriticalBracket P m t =
        c * (odlyzkoCriticalReal t * Real.cos (t * x)) := by
    rw [odlyzkoPrimePowerCriticalBracket_eq]
    dsimp [q, n, x, c]
    ring
  calc
    (∫ t : ℝ, odlyzkoCriticalReal t *
        odlyzkoPrimePowerCriticalBracket P m t) =
        ∫ t : ℝ, c *
          (odlyzkoCriticalReal t * Real.cos (t * x)) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = c * ∫ t : ℝ,
        odlyzkoCriticalReal t * Real.cos (t * x) := by
      rw [integral_const_mul]
    _ = c * (2 * Real.pi * odlyzkoF4 x) := by
      rw [show (∫ t : ℝ,
          odlyzkoCriticalReal t * Real.cos (t * x)) =
            2 * Real.pi * odlyzkoF4 x by
        simpa only [odlyzkoCriticalReal] using
          odlyzkoPhi_critical_cosine_inversion x]
    _ = 2 * Real.pi * odlyzkoPrimeTerm P (m + 1) := by
      unfold odlyzkoPrimeTerm
      dsimp [q, n, x, c]
      ring

/-- After the source normalization by `2π`, one critical prime-power bracket
is exactly one term of the complete prime correction. -/
theorem odlyzkoPrimePowerCriticalBracket_average
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    1 / (2 * Real.pi) *
        (∫ t : ℝ, odlyzkoCriticalReal t *
          odlyzkoPrimePowerCriticalBracket P m t) =
      odlyzkoPrimeTerm P (m + 1) := by
  rw [odlyzkoPrimePowerCriticalBracket_integral]
  field_simp [Real.pi_ne_zero]

/-- The finite transformed prime bracket with the same norm and exponent
cutoffs as `odlyzkoPrimeCorrectionPartial`. -/
def odlyzkoPrimeCriticalBracketPartial
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) (t : ℝ) : ℝ :=
  ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
    ∑ j ∈ Finset.range M, odlyzkoPrimePowerCriticalBracket P j t

/-- The finite critical-line bracket is integrable against the test
transform, so its finite sums may be interchanged with the integral. -/
theorem odlyzkoCritical_mul_primeBracketPartial_integrable
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) :
    Integrable
      (fun t : ℝ ↦ odlyzkoCriticalReal t *
        odlyzkoPrimeCriticalBracketPartial K N M t) volume := by
  unfold odlyzkoPrimeCriticalBracketPartial
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro P hP
  apply integrable_finsetSum
  intro j hj
  exact odlyzkoCritical_mul_primePowerBracket_integrable P j

/-- The integrated finite critical-line bracket is exactly `2π` times the
finite Odlyzko prime correction. -/
theorem odlyzkoPrimeCriticalBracketPartial_integral
    (K : Type*) [Field K] [NumberField K] (N M : ℕ) :
    (∫ t : ℝ, odlyzkoCriticalReal t *
      odlyzkoPrimeCriticalBracketPartial K N M t) =
        2 * Real.pi * odlyzkoPrimeCorrectionPartial K N M := by
  unfold odlyzkoPrimeCriticalBracketPartial
  simp_rw [Finset.mul_sum]
  calc
    (∫ t : ℝ, ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
        ∑ j ∈ Finset.range M,
          odlyzkoCriticalReal t *
            odlyzkoPrimePowerCriticalBracket P j t) =
        ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
          ∫ t : ℝ, ∑ j ∈ Finset.range M,
            odlyzkoCriticalReal t *
              odlyzkoPrimePowerCriticalBracket P j t := by
      apply integral_finsetSum
      intro P hP
      apply integrable_finsetSum
      intro j hj
      exact odlyzkoCritical_mul_primePowerBracket_integrable P j
    _ = ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
        ∑ j ∈ Finset.range M,
          ∫ t : ℝ, odlyzkoCriticalReal t *
            odlyzkoPrimePowerCriticalBracket P j t := by
      apply Finset.sum_congr rfl
      intro P hP
      apply integral_finsetSum
      intro j hj
      exact odlyzkoCritical_mul_primePowerBracket_integrable P j
    _ = ∑ P ∈ odlyzkoPrimePlacesUpTo K N,
        ∑ j ∈ Finset.range M,
          2 * Real.pi * odlyzkoPrimeTerm P (j + 1) := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro j hj
      exact odlyzkoPrimePowerCriticalBracket_integral P j
    _ = 2 * Real.pi * odlyzkoPrimeCorrectionPartial K N M := by
      unfold odlyzkoPrimeCorrectionPartial
      simp_rw [Finset.mul_sum]

/-- In the source normalization, the complete finite-support prime bracket is
the complete Odlyzko prime correction. -/
theorem odlyzkoPrimeCriticalBracket_average
    (K : Type*) [Field K] [NumberField K] :
    1 / (2 * Real.pi) *
        (∫ t : ℝ, odlyzkoCriticalReal t *
          odlyzkoPrimeCriticalBracketPartial K 4095 11 t) =
      odlyzkoPrimeCorrection K := by
  rw [odlyzkoPrimeCriticalBracketPartial_integral,
    odlyzkoPrimeCorrection_eq_finite]
  field_simp [Real.pi_ne_zero]

end

end TraceEuclidean
