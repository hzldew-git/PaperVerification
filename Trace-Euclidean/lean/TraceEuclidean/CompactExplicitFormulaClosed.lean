import TraceEuclidean.CompactExplicitFormulaArchimedeanShift

/-!
# Closed explicit formula for normalized compact kernels

This module combines the generic completed-zeta contour with the endpoint,
archimedean, and Euler prime-ideal evaluations.  No explicit-formula theorem
is supplied as a hypothesis.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

namespace CompactExplicitFormulaKernel

variable (Q : CompactExplicitFormulaKernel)

/-- The ordinary Dedekind-zeta contribution on the right vertical line. -/
def primeLineIntegrand
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℂ :=
  Q.phi ((2 : ℂ) + (t : ℂ) * I) *
    logDeriv (NumberField.dedekindZeta K)
      ((2 : ℂ) + (t : ℂ) * I)

/-- The folded completed-zeta integrand is the sum of twice the endpoint,
archimedean, and ordinary-zeta contributions. -/
theorem completedVerticalPair_decomposition
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    Q.toCompletedExplicitFormulaWeight.completedVerticalPair K t =
      2 * Q.endpointIntegrand ((2 : ℂ) + (t : ℂ) * I) +
        2 * Q.archimedeanIntegrand K ((2 : ℂ) + (t : ℂ) * I) +
        2 * Q.primeLineIntegrand K t := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  rw [CompletedExplicitFormulaWeight.completedVerticalPair_eq_two_mul]
  change
    2 * (Q.phi s *
        logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K) s) =
      2 * Q.endpointIntegrand s +
        2 * Q.archimedeanIntegrand K s +
        2 * (Q.phi s * logDeriv (NumberField.dedekindZeta K) s)
  rw [DedekindZeta.LogDeriv.logDeriv_completedZetaPoleRemoved K hs]
  rw [endpointIntegrand, odlyzkoEndpointPolynomial_logDeriv hs0 hs1]
  simp only [archimedeanIntegrand]
  ring

/-- Twice the right-line archimedean contribution is integrable. -/
theorem archimedean_twice_right_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * Q.archimedeanIntegrand K
      ((2 : ℂ) + (t : ℂ) * I)) volume := by
  have h := Q.archimedeanIntegrand_vertical_integrable K
    (σ := (2 : ℝ)) (by norm_num) (by norm_num)
  have h' : Integrable (fun t : ℝ ↦
      Q.archimedeanIntegrand K ((2 : ℂ) + (t : ℂ) * I)) volume := by
    simpa using h
  exact h'.const_mul 2

/-- Twice the ordinary-zeta contribution is integrable. -/
theorem primeLine_twice_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦ 2 * Q.primeLineIntegrand K t) volume := by
  have hPair :=
    Q.toCompletedExplicitFormulaWeight.completedVerticalPair_integrable K
  have hEndpoint := Q.endpoint_twice_right_integrable
  have hArch := Q.archimedean_twice_right_integrable K
  apply ((hPair.sub hEndpoint).sub hArch).congr
  filter_upwards with t
  change Q.toCompletedExplicitFormulaWeight.completedVerticalPair K t -
      2 * Q.endpointIntegrand ((2 : ℂ) + (t : ℂ) * I) -
      2 * Q.archimedeanIntegrand K ((2 : ℂ) + (t : ℂ) * I) =
    2 * Q.primeLineIntegrand K t
  rw [Q.completedVerticalPair_decomposition K t]
  ring

/-- The folded vertical integral splits into the three evaluated pieces. -/
theorem completedVerticalPair_integral_decomposition
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ,
      Q.toCompletedExplicitFormulaWeight.completedVerticalPair K t) =
      (∫ t : ℝ, 2 * Q.endpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I)) +
        (∫ t : ℝ, 2 * Q.archimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I)) +
        ∫ t : ℝ, 2 * Q.primeLineIntegrand K t := by
  have hEndpoint := Q.endpoint_twice_right_integrable
  have hArch := Q.archimedean_twice_right_integrable K
  have hPrime := Q.primeLine_twice_integrable K
  calc
    _ = ∫ t : ℝ,
          (2 * Q.endpointIntegrand ((2 : ℂ) + (t : ℂ) * I) +
            2 * Q.archimedeanIntegrand K ((2 : ℂ) + (t : ℂ) * I)) +
            2 * Q.primeLineIntegrand K t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Q.completedVerticalPair_decomposition K t]
    _ = _ := by
      let f : ℝ → ℂ := fun t ↦
        2 * Q.endpointIntegrand ((2 : ℂ) + (t : ℂ) * I)
      let g : ℝ → ℂ := fun t ↦
        2 * Q.archimedeanIntegrand K ((2 : ℂ) + (t : ℂ) * I)
      let p : ℝ → ℂ := fun t ↦ 2 * Q.primeLineIntegrand K t
      have hfg := integral_add hEndpoint hArch
      have hfgp := integral_add (hEndpoint.add hArch) hPrime
      change (∫ t : ℝ, (f + g + p) t) =
        (∫ t : ℝ, f t) + (∫ t : ℝ, g t) + ∫ t : ℝ, p t
      change (∫ t : ℝ, (f + g) t) =
        (∫ t : ℝ, f t) + ∫ t : ℝ, g t at hfg
      change (∫ t : ℝ, (f + g + p) t) =
        (∫ t : ℝ, (f + g) t) + ∫ t : ℝ, p t at hfgp
      rw [hfgp, hfg]

/-- The normalized ordinary-zeta integral is minus the nonnegative
prime-ideal correction. -/
theorem primeLine_normalized_integral
    (K : Type*) [Field K] [NumberField K] :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * Q.primeLineIntegrand K t) =
      -(Q.primeCorrection K : ℂ) := by
  have hPrime := Q.phi_mul_logDeriv_dedekindZeta_integral K
  change (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, 2 *
        (Q.phi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I))) = _
  rw [integral_const_mul]
  have hPrime' :
      (∫ t : ℝ,
        Q.phi ((2 : ℂ) + (t : ℂ) * I) *
          logDeriv (NumberField.dedekindZeta K)
            ((2 : ℂ) + (t : ℂ) * I)) =
        -((Real.pi * Q.primeCorrection K : ℝ) : ℂ) := by
    simpa using hPrime
  rw [hPrime']
  have hPi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp [hPi]

/-- The real part of the normalized two-copy archimedean integral for a
totally real field. -/
theorem archimedean_normalized_integral_re_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    ((1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, 2 * Q.archimedeanIntegrand K
          ((2 : ℂ) + (t : ℂ) * I))).re =
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) +
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          (-Real.log Real.pi - Real.eulerMascheroniConstant +
            Q.realGaussIntegral) := by
  have hArch := Q.archimedean_right_twice_re_integral_totallyReal hQ0 K
  have hCoeff :
      (1 / (2 * Real.pi) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hCoeff, integral_const_mul]
  norm_num [Complex.mul_re]
  norm_num at hArch
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hPi]
  nlinarith

/-- Exact real evaluation of the normalized folded completed-zeta integral
for a totally real field. -/
theorem completedVerticalPair_normalized_integral_re_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          Q.toCompletedExplicitFormulaWeight.completedVerticalPair K t).re =
      (Q.phi 0 + Q.phi 1).re +
        Real.log (((|NumberField.discr K| : ℤ) : ℝ)) +
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          (-Real.log Real.pi - Real.eulerMascheroniConstant +
            Q.realGaussIntegral) -
        Q.primeCorrection K := by
  rw [Q.completedVerticalPair_integral_decomposition K]
  simp only [mul_add, Complex.add_re]
  rw [Q.endpoint_normalized_integral,
    Q.archimedean_normalized_integral_re_totallyReal hQ0 K,
    Q.primeLine_normalized_integral K]
  norm_num
  ring

/-- The completed-zeta contour, zero positivity, and exact source evaluations
give the unconditional compact-kernel discriminant inequality. -/
theorem discriminant_log_lower_bound_totallyReal
    (hQ0 : Q.kernel 0 = 1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          (Real.log Real.pi + Real.eulerMascheroniConstant -
            Q.realGaussIntegral) +
        Q.primeCorrection K - (Q.phi 0 + Q.phi 1).re ≤
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) := by
  have hNonneg :=
    Q.toCompletedExplicitFormulaWeight.completedVerticalPair_integral_re_nonneg K
  rw [Q.completedVerticalPair_normalized_integral_re_totallyReal hQ0 K] at hNonneg
  linarith

end CompactExplicitFormulaKernel

end
end TraceEuclidean
