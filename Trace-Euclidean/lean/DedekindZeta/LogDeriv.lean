import DedekindZeta.FractionalIdealRescaling
import DedekindZeta.PrimeLogDeriv
import DedekindZeta.ZetaRegularization
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Logarithmic derivatives of the constructed completed Dedekind zeta

This file supplies the first contour-integration interface for the global
theta--Mellin continuation. On the half-plane `Re s > 1`, it identifies the
logarithmic derivative of the entire pole-removed completion with the
elementary pole factors, the archimedean factor, and the ordinary Dedekind
zeta function. It also differentiates the already proved functional
equation.

The nonvanishing of the ordinary Dedekind zeta function on `Re s > 1` is
supplied by the ideal Euler product in `DedekindZeta.IdealEulerProduct`.
-/

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex Filter Set Topology

namespace DedekindZeta.LogDeriv

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-- The theta--Mellin completion agrees locally with its defining
right-half-plane expression. -/
theorem completedZetaPoleRemoved_eventuallyEq_zeta {s : ℂ} (hs : 1 < s.re) :
    GlobalContinuation.completedZetaPoleRemoved K =ᶠ[𝓝 s]
      fun u ↦ u * (u - 1) * (ZInfty K u * NumberField.dedekindZeta K u) := by
  have hopen : IsOpen {u : ℂ | 1 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  exact GlobalContinuation.completedZetaPoleRemoved_eq_zeta K hu

/-- On the positive half-plane, the archimedean factor is locally the inverse
of the entire reciprocal multiplier times the identity function. -/
theorem ZInfty_eventuallyEq_inverse {s : ℂ} (hs : 0 < s.re) :
    ZInfty K =ᶠ[𝓝 s]
      fun u ↦ (ZetaRegularization.inverseCompletedMultiplier K u * u)⁻¹ := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have h := ZetaRegularization.inverseCompletedMultiplier_mul_of_re_pos K hu
  apply eq_inv_of_mul_eq_one_right
  simpa only [mul_assoc] using h

/-- The archimedean completion factor does not vanish in the positive
half-plane. -/
theorem ZInfty_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ZInfty K s ≠ 0 := by
  have h := ZetaRegularization.inverseCompletedMultiplier_mul_of_re_pos K hs
  exact right_ne_zero_of_mul_eq_one
    (show (ZetaRegularization.inverseCompletedMultiplier K s * s) * ZInfty K s = 1 by
      simpa only [mul_assoc] using h)

/-- The archimedean completion factor is complex differentiable throughout
the positive half-plane. -/
theorem differentiableAt_ZInfty {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (ZInfty K) s := by
  have hprod :
      (ZetaRegularization.inverseCompletedMultiplier K s * s) * ZInfty K s = 1 := by
    simpa only [mul_assoc] using
      (ZetaRegularization.inverseCompletedMultiplier_mul_of_re_pos K hs)
  have hne : ZetaRegularization.inverseCompletedMultiplier K s * s ≠ 0 :=
    left_ne_zero_of_mul_eq_one hprod
  have hInv : DifferentiableAt ℂ
      (fun u : ℂ ↦ (ZetaRegularization.inverseCompletedMultiplier K u * u)⁻¹) s :=
    (((analyticOnNhd_univ_iff_differentiable.mp
      (ZetaRegularization.inverseCompletedMultiplier_analyticOn K)) s).mul
        differentiableAt_id).inv hne
  exact hInv.congr_of_eventuallyEq (ZInfty_eventuallyEq_inverse K hs)

/-- On `Re s > 1`, the ordinary Dedekind zeta is locally the quotient of its
entire regularization by `s - 1`. -/
theorem dedekindZeta_eventuallyEq_regularized_div {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K =ᶠ[𝓝 s]
      fun u ↦ ZetaRegularization.dedekindZetaRegularized K u / (u - 1) := by
  have hopen : IsOpen {u : ℂ | 1 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu1 : u - 1 ≠ 0 := by
    intro h
    have : u = 1 := sub_eq_zero.mp h
    subst u
    norm_num at hu
  rw [ZetaRegularization.dedekindZetaRegularized_eq K hu]
  field_simp

/-- The ordinary Dedekind zeta is complex differentiable on its defining
half-plane of absolute convergence. -/
theorem differentiableAt_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    subst s
    norm_num at hs
  have hRegularized : DifferentiableAt ℂ
      (ZetaRegularization.dedekindZetaRegularized K) s :=
    (analyticOnNhd_univ_iff_differentiable.mp
      (ZetaRegularization.dedekindZetaRegularized_analyticOn K)) s
  have hQuot : DifferentiableAt ℂ
      (fun u : ℂ ↦ ZetaRegularization.dedekindZetaRegularized K u / (u - 1)) s :=
    hRegularized.div (differentiableAt_id.sub (differentiableAt_const 1)) hs1
  exact hQuot.congr_of_eventuallyEq
    (dedekindZeta_eventuallyEq_regularized_div K hs)

/-- On `Re s > 1`, the non-inverted prime Euler product is locally the
reciprocal of the ordinary Dedekind zeta function. -/
theorem primeEulerBaseProduct_eventuallyEq_inverse {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.primeEulerBaseProduct K =ᶠ[𝓝 s]
      fun u => (NumberField.dedekindZeta K u)⁻¹ := by
  have hopen : IsOpen {u : ℂ | 1 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  exact eq_inv_of_mul_eq_one_left
    (DedekindZeta.primeEulerBaseProduct_mul_dedekindZeta K hu)

/-- The non-inverted prime Euler product is differentiable on its half-plane
of absolute convergence. -/
theorem differentiableAt_primeEulerBaseProduct {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (DedekindZeta.primeEulerBaseProduct K) s := by
  have hζne : NumberField.dedekindZeta K s ≠ 0 :=
    DedekindZeta.dedekindZeta_ne_zero_of_one_lt_re K hs
  have hInv : DifferentiableAt ℂ
      (fun u => (NumberField.dedekindZeta K u)⁻¹) s :=
    (differentiableAt_dedekindZeta K hs).inv hζne
  exact hInv.congr_of_eventuallyEq
    (primeEulerBaseProduct_eventuallyEq_inverse K hs)

/-- The logarithmic derivative of Dedekind zeta on `Re s > 1` is the
negative sum of the logarithmic derivatives of the non-inverted local Euler
factors. -/
theorem logDeriv_dedekindZeta_eq_neg_tsum_primeFactor {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (NumberField.dedekindZeta K) s =
      -∑' v : HeightOneSpectrum (𝓞 K),
        logDeriv (DedekindZeta.primeEulerBaseFactor K v) s := by
  have hPne : DedekindZeta.primeEulerBaseProduct K s ≠ 0 :=
    DedekindZeta.primeEulerBaseProduct_ne_zero K hs
  have hζne : NumberField.dedekindZeta K s ≠ 0 :=
    DedekindZeta.dedekindZeta_ne_zero_of_one_lt_re K hs
  have hPdiff : DifferentiableAt ℂ
      (DedekindZeta.primeEulerBaseProduct K) s :=
    differentiableAt_primeEulerBaseProduct K hs
  have hζdiff : DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
    differentiableAt_dedekindZeta K hs
  have hmul := logDeriv_mul
    (f := DedekindZeta.primeEulerBaseProduct K)
    (g := NumberField.dedekindZeta K) s hPne hζne hPdiff hζdiff
  have hev :
      (fun u => DedekindZeta.primeEulerBaseProduct K u *
        NumberField.dedekindZeta K u) =ᶠ[𝓝 s] fun _ => (1 : ℂ) := by
    have hopen : IsOpen {u : ℂ | 1 < u.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with u hu
    exact DedekindZeta.primeEulerBaseProduct_mul_dedekindZeta K hu
  have hzero : logDeriv
      (fun u => DedekindZeta.primeEulerBaseProduct K u *
        NumberField.dedekindZeta K u) s = 0 := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    simp
  have hadd :
      logDeriv (DedekindZeta.primeEulerBaseProduct K) s +
        logDeriv (NumberField.dedekindZeta K) s = 0 := by
    calc
      _ = logDeriv
          (fun u => DedekindZeta.primeEulerBaseProduct K u *
            NumberField.dedekindZeta K u) s := hmul.symm
      _ = 0 := hzero
  calc
    logDeriv (NumberField.dedekindZeta K) s =
        -logDeriv (DedekindZeta.primeEulerBaseProduct K) s :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hadd)
    _ = -∑' v : HeightOneSpectrum (𝓞 K),
          logDeriv (DedekindZeta.primeEulerBaseFactor K v) s := by
      rw [DedekindZeta.logDeriv_primeEulerBaseProduct_eq_tsum K hs]

/-- Expanded prime-ideal Euler-factor formula for the logarithmic derivative
of Dedekind zeta on `Re s > 1`. -/
theorem logDeriv_dedekindZeta_eq_neg_tsum_primeIdeal {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (NumberField.dedekindZeta K) s =
      -∑' v : HeightOneSpectrum (𝓞 K),
        Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          DedekindZeta.primeEulerParameter K v s /
            DedekindZeta.primeEulerBaseFactor K v s := by
  rw [logDeriv_dedekindZeta_eq_neg_tsum_primeFactor K hs]
  congr 1
  apply tsum_congr
  intro v
  exact DedekindZeta.logDeriv_primeEulerBaseFactor K v s

/-- Prime-power form of the Dedekind-zeta logarithmic derivative.  The double
series is absolutely convergent, so its product indexing is canonical. -/
theorem logDeriv_dedekindZeta_eq_neg_tsum_primePowers {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (NumberField.dedekindZeta K) s =
      -∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
        DedekindZeta.primePowerLogTerm K p.1 p.2 s := by
  rw [logDeriv_dedekindZeta_eq_neg_tsum_primeFactor K hs]
  congr 1
  rw [DedekindZeta.tsum_primePowerLogTerm_prod K hs]
  apply tsum_congr
  intro v
  exact DedekindZeta.logDeriv_primeEulerBaseFactor_eq_tsum_primePowers K v hs

/-- On `Re s > 1`, the logarithmic derivative of the entire pole-removed
completion splits into the two elementary pole-removal factors, the
archimedean factor, and the ordinary Dedekind zeta logarithmic derivative. -/
theorem logDeriv_completedZetaPoleRemoved {s : ℂ} (hs : 1 < s.re)
    : logDeriv (GlobalContinuation.completedZetaPoleRemoved K) s =
      1 / s + 1 / (s - 1) + logDeriv (ZInfty K) s +
        logDeriv (NumberField.dedekindZeta K) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    subst s
    norm_num at hs
  have hZ : ZInfty K s ≠ 0 := ZInfty_ne_zero_of_re_pos K (by linarith)
  have hζ : NumberField.dedekindZeta K s ≠ 0 :=
    DedekindZeta.dedekindZeta_ne_zero_of_one_lt_re K hs
  have hId : DifferentiableAt ℂ (fun u : ℂ ↦ u) s := differentiableAt_id
  have hSub : DifferentiableAt ℂ (fun u : ℂ ↦ u - 1) s :=
    differentiableAt_id.sub (differentiableAt_const 1)
  have hZdiff : DifferentiableAt ℂ (ZInfty K) s :=
    differentiableAt_ZInfty K (by linarith)
  have hζdiff : DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
    differentiableAt_dedekindZeta K hs
  have hev := completedZetaPoleRemoved_eventuallyEq_zeta K hs
  have heq :
      logDeriv (GlobalContinuation.completedZetaPoleRemoved K) s =
        logDeriv
          (fun u : ℂ ↦ (u * (u - 1)) *
            (ZInfty K u * NumberField.dedekindZeta K u)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hOuter := logDeriv_mul
    (f := fun u : ℂ ↦ u * (u - 1))
    (g := fun u : ℂ ↦ ZInfty K u * NumberField.dedekindZeta K u)
    s (mul_ne_zero hs0 hs1) (mul_ne_zero hZ hζ)
      (hId.mul hSub) (hZdiff.mul hζdiff)
  have hElementary := logDeriv_mul
    (f := fun u : ℂ ↦ u) (g := fun u : ℂ ↦ u - 1)
    s hs0 hs1 hId hSub
  have hCompleted := logDeriv_mul
    (f := ZInfty K) (g := NumberField.dedekindZeta K)
    s hZ hζ hZdiff hζdiff
  rw [heq, hOuter, hElementary, hCompleted]
  have hLogSub : logDeriv (fun u : ℂ ↦ u - 1) s = 1 / (s - 1) := by
    simp [logDeriv_apply]
  rw [logDeriv_id', hLogSub]
  ring

/-- Differentiating the completed functional equation gives the reflection
law for its logarithmic derivative. -/
theorem logDeriv_completedZetaPoleRemoved_one_sub (s : ℂ) :
    logDeriv (GlobalContinuation.completedZetaPoleRemoved K) (1 - s) =
      -logDeriv (GlobalContinuation.completedZetaPoleRemoved K) s := by
  have hcomp : GlobalContinuation.completedZetaPoleRemoved K =
      GlobalContinuation.completedZetaPoleRemoved K ∘ (fun u : ℂ ↦ 1 - u) := by
    funext u
    exact FractionalIdealRescaling.completedZetaPoleRemoved_reflection K u
  have hd : DifferentiableAt ℂ
      (GlobalContinuation.completedZetaPoleRemoved K) (1 - s) :=
    (analyticOnNhd_univ_iff_differentiable.mp
      (GlobalContinuation.completedZetaPoleRemoved_analyticOn K)) (1 - s)
  have hg : DifferentiableAt ℂ (fun u : ℂ ↦ 1 - u) s :=
    (differentiableAt_const 1).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ ↦ 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

end

end DedekindZeta.LogDeriv
