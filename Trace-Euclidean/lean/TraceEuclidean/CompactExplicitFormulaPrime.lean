import TraceEuclidean.CompactExplicitFormulaTransform
import TraceEuclidean.OdlyzkoPrimeTransform

/-!
# Prime-ideal term for compact explicit-formula kernels

The Euler product on `Re(s)=2` is transformed by the generic compact source
kernel.  The resulting correction is a sum of nonnegative terms, so it can be
dropped in the lower-bound application.
-/

namespace TraceEuclidean

noncomputable section

open Complex FourierTransform IsDedekindDomain MeasureTheory
open scoped NumberField RealInnerProductSpace

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)
variable {K : Type*} [Field K] [NumberField K]

private theorem prime_absNorm_one_lt
    (P : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm P.asIdeal := by
  by_contra! h
  apply Ideal.IsPrime.ne_top P.isPrime
  rw [← Ideal.absNorm_eq_one_iff]
  have hpos : 0 < Ideal.absNorm P.asIdeal := by
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  omega

/-- The source-normalized prime-power correction attached to a compact
kernel. -/
def primeTerm (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) : ℝ :=
  let q : ℝ := Ideal.absNorm P.asIdeal
  2 * Real.log q * Q.kernel (Real.log (q ^ m)) /
    q ^ ((m : ℝ) / 2)

theorem primeTerm_nonneg (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    0 ≤ Q.primeTerm P m := by
  have hqNat : 1 < Ideal.absNorm P.asIdeal :=
    prime_absNorm_one_lt P
  have hq : (0 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hqOne : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by exact_mod_cast hqNat.le
  unfold primeTerm
  dsimp only
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg hqOne))
      (Q.nonneg _))
    (Real.rpow_nonneg hq.le _)

/-- Complete nonnegative prime-ideal correction for the compact kernel. -/
def primeCorrection (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
    Q.primeTerm p.1 (p.2 + 1)

theorem primeCorrection_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ Q.primeCorrection K := by
  unfold primeCorrection
  exact tsum_nonneg fun p ↦ Q.primeTerm_nonneg p.1 (p.2 + 1)

/-- One Euler prime-power integrand is integrable on the right contour line. -/
theorem phi_mul_primePowerLogTerm_integrable
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Integrable
      (fun t : ℝ ↦
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) volume := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℂ := (Real.log q * Real.exp (-2 * x) : ℝ)
  have hphase := Q.phi_vertical_phase_integrable 2 x (by norm_num) (by norm_num)
  apply (hphase.const_mul c).congr
  filter_upwards with t
  rw [odlyzkoPrimePowerLogTerm_vertical_eq]
  dsimp [q, n, x, c]
  ring

/-- The transform of one Euler prime-power term is exactly half of the
corresponding source correction term. -/
theorem phi_mul_primePowerLogTerm_integral
    (P : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    (∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ((Real.pi * Q.primeTerm P (m + 1) : ℝ) : ℂ) := by
  let q : ℝ := Ideal.absNorm P.asIdeal
  let n : ℕ := m + 1
  let x : ℝ := Real.log (q ^ n)
  let c : ℂ := (Real.log q * Real.exp (-2 * x) : ℝ)
  have hqNat : 1 < Ideal.absNorm P.asIdeal :=
    prime_absNorm_one_lt P
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans hqNat)
  have hpoint (t : ℝ) :
      Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        c * (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
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
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          DedekindZeta.primePowerLogTerm K P m
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ, c *
          (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
            Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = c * ∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      rw [integral_const_mul]
    _ = c * ((2 * Real.pi : ℝ) • Q.tilted (2 - 1 / 2) x) := by
      rw [Q.phi_vertical_inversion_integral 2 x (by norm_num) (by norm_num)]
    _ = ((Real.pi * Q.primeTerm P (m + 1) : ℝ) : ℂ) := by
      unfold tilted primeTerm
      have hreal :
          Real.log q * Real.exp (-2 * x) *
              (2 * Real.pi *
                (Real.exp ((2 - 1 / 2) * x) * Q.kernel x)) =
            Real.pi *
              (2 * Real.log q * Q.kernel x / q ^ ((n : ℝ) / 2)) := by
        calc
          _ = 2 * Real.pi * Real.log q * Q.kernel x *
              (Real.exp (-2 * x) * Real.exp ((2 - 1 / 2) * x)) := by ring
          _ = 2 * Real.pi * Real.log q * Q.kernel x *
              Real.exp (-2 * x + (2 - 1 / 2) * x) := by
                rw [Real.exp_add]
          _ = 2 * Real.pi * Real.log q * Q.kernel x *
              Real.exp (-(x / 2)) := by
                rw [show -2 * x + (2 - 1 / 2) * x = -(x / 2) by ring]
          _ = _ := by
            rw [hexpHalf, div_eq_mul_inv]
            ring
      have hcast := congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
      simpa [c, q, n, x, Algebra.smul_def] using hcast

/-- Interchanging the complete Euler prime-power sum with the right-line
integral gives the full compact-kernel correction. -/
theorem phi_mul_primePowerLogTerm_tsum_integral
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
      ((Real.pi * Q.primeCorrection K : ℝ) : ℂ) := by
  letI : Countable (HeightOneSpectrum (𝓞 K)) :=
    odlyzkoPrimePlaces_countable K
  let F : (HeightOneSpectrum (𝓞 K) × ℕ) → ℝ → ℂ := fun p t ↦
    Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
      DedekindZeta.primePowerLogTerm K p.1 p.2
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  let C : ℝ := ∫ t : ℝ, ‖Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
  have hFint (p : HeightOneSpectrum (𝓞 K) × ℕ) :
      Integrable (F p) volume := by
    simpa only [F] using Q.phi_mul_primePowerLogTerm_integrable p.1 p.2
  have hnormConst (p : HeightOneSpectrum (𝓞 K) × ℕ) (t : ℝ) :
      ‖DedekindZeta.primePowerLogTerm K p.1 p.2
          (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖DedekindZeta.primePowerLogTerm K p.1 p.2 ((2 : ℝ) : ℂ)‖ := by
    rw [DedekindZeta.norm_primePowerLogTerm,
      DedekindZeta.norm_primePowerLogTerm]
    norm_num [Complex.mul_re]
  have hFnorm (p : HeightOneSpectrum (𝓞 K) × ℕ) :
      (∫ t : ℝ, ‖F p t‖) =
        ‖DedekindZeta.primePowerLogTerm K p.1 p.2 ((2 : ℝ) : ℂ)‖ * C := by
    dsimp only [F, C]
    simp_rw [norm_mul, hnormConst p]
    calc
      (∫ t : ℝ, ‖Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
          ‖DedekindZeta.primePowerLogTerm K p.1 p.2 ((2 : ℝ) : ℂ)‖) =
          ∫ t : ℝ,
            ‖DedekindZeta.primePowerLogTerm K p.1 p.2 ((2 : ℝ) : ℂ)‖ *
              ‖Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = ‖DedekindZeta.primePowerLogTerm K p.1 p.2 ((2 : ℝ) : ℂ)‖ *
          ∫ t : ℝ, ‖Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [integral_const_mul]
  have habs :=
    DedekindZeta.summable_norm_primePowerLogTerm K (by norm_num : 1 < (((2 : ℝ) : ℂ).re))
  have hFsum : Summable (fun p : HeightOneSpectrum (𝓞 K) × ℕ ↦
      ∫ t : ℝ, ‖F p t‖) := by
    exact (habs.mul_right C).congr fun p ↦ (hFnorm p).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    hFint hFsum
  calc
    (∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) =
        ∫ t : ℝ, ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, F p t := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [F]
      rw [← tsum_mul_left]
    _ = ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
        ∫ t : ℝ, F p t := hswap.symm
    _ = ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
        ((Real.pi * Q.primeTerm p.1 (p.2 + 1) : ℝ) : ℂ) := by
      apply tsum_congr
      intro p
      simpa only [F] using Q.phi_mul_primePowerLogTerm_integral p.1 p.2
    _ = ((Real.pi * Q.primeCorrection K : ℝ) : ℂ) := by
      rw [show (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
          ((Real.pi * Q.primeTerm p.1 (p.2 + 1) : ℝ) : ℂ)) =
          (Real.pi : ℂ) *
            ∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
              (Q.primeTerm p.1 (p.2 + 1) : ℂ) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro p
        norm_num]
      rw [← Complex.ofReal_tsum]
      unfold primeCorrection
      norm_num

/-- On the right line, the actual Dedekind-zeta logarithmic derivative gives
minus the full nonnegative compact-kernel prime correction. -/
theorem phi_mul_logDeriv_dedekindZeta_integral
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          logDeriv (NumberField.dedekindZeta K)
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      -((Real.pi * Q.primeCorrection K : ℝ) : ℂ) := by
  letI : Countable (HeightOneSpectrum (𝓞 K)) :=
    odlyzkoPrimePlaces_countable K
  calc
    (∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          logDeriv (NumberField.dedekindZeta K)
            (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ,
          -(Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
              DedekindZeta.primePowerLogTerm K p.1 p.2
                (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards with t
      have hline : 1 < ((((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) := by
        norm_num [Complex.mul_re]
      rw [DedekindZeta.LogDeriv.logDeriv_dedekindZeta_eq_neg_tsum_primePowers
        K hline]
      ring
    _ = -(∫ t : ℝ,
        Q.phi (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
            DedekindZeta.primePowerLogTerm K p.1 p.2
              (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
      rw [integral_neg]
    _ = -((Real.pi * Q.primeCorrection K : ℝ) : ℂ) := by
      rw [Q.phi_mul_primePowerLogTerm_tsum_integral K]

end CompactExplicitFormulaKernel

end
end TraceEuclidean
