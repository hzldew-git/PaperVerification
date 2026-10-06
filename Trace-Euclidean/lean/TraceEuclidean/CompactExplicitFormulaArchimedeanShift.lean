import TraceEuclidean.CompactExplicitFormulaArchimedean

/-!
# Shifting a compact explicit-formula archimedean term

The analytic shift is uniform for every compact source kernel satisfying the
fourth-power transform bound.  The final theorem evaluates the two folded
archimedean copies for a totally real number field.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)

/-- The archimedean part of the completed-zeta contour integrand. -/
def archimedeanIntegrand
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  Q.phi s * logDeriv (DedekindZeta.ZInfty K) s

/-- Fourth-power transform decay absorbs the logarithmic growth of the
archimedean logarithmic derivative uniformly on the shift strip. -/
theorem exists_archimedean_strip_majorant
    (K : Type*) [Field K] [NumberField K] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖Q.archimedeanIntegrand K s‖ ≤
        M / (1 + |s.im|) ^ 2 := by
  obtain ⟨D, hD, hPhi⟩ := Q.phi_exists_wideFourthPowerBound
  obtain ⟨C, hC, hLog⟩ := exists_logDeriv_ZInfty_growth_strip K
  refine ⟨D * C, mul_nonneg hD hC.le, fun s hs0 hs1 ↦ ?_⟩
  let u : ℝ := 1 + |s.im|
  have hu : 0 < u := by dsimp only [u]; positivity
  have hPhi' : ‖Q.phi s‖ ≤ D / u ^ 4 := by
    simpa only [u] using hPhi s (by linarith) hs1
  have hLog' : ‖logDeriv (DedekindZeta.ZInfty K) s‖ ≤
      C * Real.log (2 + |s.im|) := hLog s hs0 hs1
  have hLogPow : Real.log (2 + |s.im|) ≤ u ^ 2 := by
    have hbase := Real.log_le_sub_one_of_pos
      (show 0 < 2 + |s.im| by positivity)
    have huOne : 1 ≤ u := by dsimp only [u]; linarith [abs_nonneg s.im]
    have huSq : u ≤ u ^ 2 := by nlinarith
    dsimp only [u] at hbase ⊢
    linarith
  rw [archimedeanIntegrand, norm_mul]
  calc
    ‖Q.phi s‖ * ‖logDeriv (DedekindZeta.ZInfty K) s‖ ≤
        (D / u ^ 4) * (C * Real.log (2 + |s.im|)) :=
      mul_le_mul hPhi' hLog' (norm_nonneg _)
        (div_nonneg hD (pow_nonneg hu.le 4))
    _ ≤ (D / u ^ 4) * (C * u ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLogPow hC.le)
        (div_nonneg hD (pow_nonneg hu.le 4))
    _ = D * C / u ^ 2 := by field_simp

/-- The compact archimedean contour integrand is holomorphic on the shift
strip. -/
lemma archimedeanIntegrand_differentiableAt
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Q.archimedeanIntegrand K) s := by
  exact Q.phi_differentiable.differentiableAt.mul
    (logDeriv_ZInfty_differentiableAt_of_re_pos K hs)

/-- Integrability on every vertical line in the shift strip. -/
theorem archimedeanIntegrand_vertical_integrable
    (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 2) :
    Integrable (fun t : ℝ ↦
      Q.archimedeanIntegrand K (σ + t * I)) volume := by
  obtain ⟨M, -, hMajorant⟩ := Q.exists_archimedean_strip_majorant K
  apply Analytic.integrable_line
  · intro t
    apply Q.archimedeanIntegrand_differentiableAt
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_self, add_zero]
    linarith
  · exact odlyzkoCriticalMajorant_two_integrable M
  · intro t
    have h := hMajorant (((σ : ℝ) : ℂ) + (t : ℂ) * I)
      (by norm_num at hσ0 ⊢; exact hσ0)
      (by norm_num at hσ1 ⊢; exact hσ1)
    simpa using h

/-- The right-line archimedean integral equals its critical-line value. -/
theorem archimedean_right_eq_critical
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ, Q.archimedeanIntegrand K
      ((2 : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, Q.archimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  obtain ⟨M, -, hMajorant⟩ := Q.exists_archimedean_strip_majorant K
  have hdiff : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      DifferentiableAt ℂ (Q.archimedeanIntegrand K) s := by
    intro s hs0 _
    exact Q.archimedeanIntegrand_differentiableAt K (by linarith)
  have hbound : ∀ (σ t : ℝ), (1 / 2 : ℝ) ≤ σ → σ ≤ 2 →
      ‖Q.archimedeanIntegrand K (((σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        odlyzkoQuadraticMajorant M t := by
    intro σ t hs0 hs1
    change ‖Q.archimedeanIntegrand K (((σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      M / (1 + |t|) ^ 2
    simpa using hMajorant (((σ : ℝ) : ℂ) + (t : ℂ) * I)
      (by norm_num at hs0 ⊢; exact hs0)
      (by norm_num at hs1 ⊢; exact hs1)
  have hshift := Analytic.vertical_line_shift
    (f := Q.archimedeanIntegrand K)
    (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) hdiff
    (odlyzkoQuadraticMajorant_integrable M) hbound
    (odlyzkoQuadraticMajorant_tendsto_atTop M)
    (odlyzkoQuadraticMajorant_tendsto_atBot M)
  norm_num at hshift ⊢
  exact hshift

/-- On the critical line the two real copies form the symmetric Gamma
bracket. -/
theorem archimedean_critical_twice_re
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    2 * (Q.archimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
      Q.criticalReal t *
        (logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) + (t : ℂ) * I) +
          logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) - (t : ℂ) * I)).re := by
  have him :
      (Q.phi ((1 / 2 : ℂ) + (t : ℂ) * I)).im = 0 := by
    convert Q.phi_critical_im_eq_zero t using 1 <;> norm_num
  have hre :
      Q.criticalReal t =
        (Q.phi ((1 / 2 : ℂ) + (t : ℂ) * I)).re := by
    unfold criticalReal
    congr 2
    norm_num
  rw [archimedeanIntegrand, Complex.mul_re, him]
  rw [hre]
  rw [← logDeriv_ZInfty_critical_twice_re K t]
  ring

/-- For a totally real field, the symmetric archimedean bracket is
integrable against every normalized compact transform. -/
theorem critical_mul_archimedeanBracket_re_integrable_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    Integrable
      (fun t : ℝ ↦
        Q.criticalReal t *
          (logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) + (t : ℂ) * I) +
            logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) - (t : ℂ) * I)).re) volume := by
  let logD : ℝ := Real.log (((|NumberField.discr K| : ℤ) : ℝ))
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  have hdisc := Q.criticalReal_integrable.const_mul logD
  have hreal := (Q.critical_mul_realPlaceBracket_integrable hQ0).const_mul r
  have hsum := hdisc.add hreal
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [odlyzkoArchimedeanBracket_re_eq K t,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
  dsimp only [logD, r]
  ring

/-- Exact totally real archimedean pairing. -/
theorem critical_mul_archimedeanBracket_re_integral_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    (∫ t : ℝ,
      Q.criticalReal t *
        (logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) + (t : ℂ) * I) +
          logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) - (t : ℂ) * I)).re) =
      2 * Real.pi *
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) +
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            (-Real.log Real.pi - Real.eulerMascheroniConstant +
              Q.realGaussIntegral)) := by
  let logD : ℝ := Real.log (((|NumberField.discr K| : ℤ) : ℝ))
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  have hdisc := Q.criticalReal_integrable.const_mul logD
  have hreal := (Q.critical_mul_realPlaceBracket_integrable hQ0).const_mul r
  calc
    _ = ∫ t : ℝ,
          logD * Q.criticalReal t +
            r * (Q.criticalReal t *
              (-Real.log Real.pi +
                (Complex.digamma
                  ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [odlyzkoArchimedeanBracket_re_eq K t,
        NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
      dsimp only [logD, r]
      ring
    _ = logD * (∫ t : ℝ, Q.criticalReal t) +
        r * (∫ t : ℝ, Q.criticalReal t *
          (-Real.log Real.pi +
            (Complex.digamma
              ((1 / 4 : ℂ) + (t / 2 : ℝ) * I)).re)) := by
      rw [integral_add hdisc hreal, integral_const_mul,
        integral_const_mul]
    _ = _ := by
      rw [Q.criticalReal_integral hQ0,
        Q.critical_mul_realPlaceBracket_integral hQ0]
      dsimp only [logD, r]
      ring

/-- Exact real part of the two folded right-line archimedean copies in the
totally real case. -/
theorem archimedean_right_twice_re_integral_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    2 * (∫ t : ℝ, Q.archimedeanIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)).re =
      2 * Real.pi *
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) +
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            (-Real.log Real.pi - Real.eulerMascheroniConstant +
              Q.realGaussIntegral)) := by
  rw [Q.archimedean_right_eq_critical K]
  have hint := Q.archimedeanIntegrand_vertical_integrable K
    (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hint' : Integrable (fun t : ℝ ↦
      Q.archimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)) volume := by
    convert hint using 1 <;> norm_num
  have hre :
      (∫ t : ℝ, (Q.archimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re) =
        (∫ t : ℝ, Q.archimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re :=
    integral_re hint'
  calc
    2 * (∫ t : ℝ, Q.archimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re =
        2 * ∫ t : ℝ, (Q.archimedeanIntegrand K
          ((1 / 2 : ℂ) + (t : ℂ) * I)).re := congrArg (2 * ·) hre.symm
    _ = ∫ t : ℝ, 2 * (Q.archimedeanIntegrand K
        ((1 / 2 : ℂ) + (t : ℂ) * I)).re := by rw [integral_const_mul]
    _ = ∫ t : ℝ, Q.criticalReal t *
          (logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) + (t : ℂ) * I) +
            logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) - (t : ℂ) * I)).re := by
      apply integral_congr_ae
      filter_upwards with t
      exact Q.archimedean_critical_twice_re K t
    _ = _ := Q.critical_mul_archimedeanBracket_re_integral_totallyReal hQ0 K

end CompactExplicitFormulaKernel

end
end TraceEuclidean
