import DedekindZeta.DigammaVertical
import DedekindZeta.DigammaIdentities
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gauss integral bridge for the real part of digamma

This module derives the Laplace-cosine identities needed to convert the
vertical-line digamma series into Gauss' integral representation. The target
normalization is the one used by the two hyperbolic archimedean integrals in
Odlyzko's explicit formula.
-/

noncomputable section

namespace DedekindZeta.DigammaIntegral

open Complex MeasureTheory Set

/-- The elementary Laplace transform of a cosine. -/
theorem integral_exp_neg_mul_cos_Ioi {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-c * x) * Real.cos (t * x)) =
      c / (c ^ 2 + t ^ 2) := by
  let q : ℂ := (-c : ℂ) + (t : ℂ) * I
  have hq : q.re < 0 := by
    dsimp [q]
    simpa using neg_lt_zero.mpr hc
  have hqint : IntegrableOn (fun x : ℝ ↦ Complex.exp (q * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq 0
  have hreint : IntegrableOn (fun x : ℝ ↦ (Complex.exp (q * x)).re) (Ioi 0) :=
    Complex.reCLM.integrable_comp hqint
  have hpoint (x : ℝ) :
      (Complex.exp (q * x)).re = Real.exp (-c * x) * Real.cos (t * x) := by
    dsimp [q]
    rw [Complex.exp_re]
    congr 1 <;> simp
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ hpoint x)]
  have hre :
      (∫ x in Ioi (0 : ℝ), (Complex.exp (q * x)).re) =
        (∫ x in Ioi (0 : ℝ), Complex.exp (q * x)).re := by
    exact integral_re hqint
  rw [hre]
  rw [integral_exp_mul_complex_Ioi hq 0]
  simp [q, Complex.div_re, Complex.normSq_apply]
  ring

/-- Integrability of the Laplace-cosine kernel on the positive half-line. -/
theorem integrableOn_exp_neg_mul_cos_Ioi {c : ℝ} (hc : 0 < c) (t : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-c * x) * Real.cos (t * x)) (Ioi 0) := by
  let q : ℂ := (-c : ℂ) + (t : ℂ) * I
  have hq : q.re < 0 := by
    dsimp [q]
    simpa using neg_lt_zero.mpr hc
  have hqint : IntegrableOn (fun x : ℝ ↦ Complex.exp (q * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hq 0
  have hreint : IntegrableOn (fun x : ℝ ↦ (Complex.exp (q * x)).re) (Ioi 0) :=
    Complex.reCLM.integrable_comp hqint
  exact hreint.congr_fun (fun x _ ↦ by
    dsimp [q]
    rw [Complex.exp_re]
    congr 1 <;> simp) measurableSet_Ioi

/-- The nonnegative Laplace summand underlying Gauss' digamma integral. -/
def gaussTerm (a t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) + 1) * x) -
    Real.exp (-((n : ℝ) + 1 + a) * x) * Real.cos (t * x)

theorem gaussTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussTerm a t n x := by
  have hcos :
      Real.exp (-((n : ℝ) + 1 + a) * x) * Real.cos (t * x) ≤
        Real.exp (-((n : ℝ) + 1 + a) * x) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.cos_le_one (t * x)) (Real.exp_pos _).le
  have hexp :
      Real.exp (-((n : ℝ) + 1 + a) * x) ≤
        Real.exp (-((n : ℝ) + 1) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold gaussTerm
  linarith

theorem gaussTerm_integrableOn {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    IntegrableOn (gaussTerm a t n) (Ioi 0) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hna : 0 < (n : ℝ) + 1 + a := by positivity
  have hfirst :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-((n : ℝ) + 1) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -((n : ℝ) + 1) < 0) 0
  have hsecond :
      IntegrableOn
        (fun x : ℝ ↦ Real.exp (-((n : ℝ) + 1 + a) * x) *
          Real.cos (t * x)) (Ioi 0) :=
    integrableOn_exp_neg_mul_cos_Ioi hna t
  exact hfirst.sub hsecond

theorem integral_gaussTerm {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), gaussTerm a t n x) =
      1 / ((n : ℝ) + 1) -
        ((n : ℝ) + 1 + a) /
          (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hna : 0 < (n : ℝ) + 1 + a := by positivity
  have hfirst :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-((n : ℝ) + 1) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -((n : ℝ) + 1) < 0) 0
  have hsecond := integral_exp_neg_mul_cos_Ioi hna t
  have hsecondInt :
      IntegrableOn
        (fun x : ℝ ↦ Real.exp (-((n : ℝ) + 1 + a) * x) *
          Real.cos (t * x)) (Ioi 0) :=
    integrableOn_exp_neg_mul_cos_Ioi hna t
  unfold gaussTerm
  rw [integral_sub hfirst hsecondInt,
    integral_exp_mul_Ioi (by linarith : -((n : ℝ) + 1) < 0) 0,
    hsecond]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Since each Gauss summand is nonnegative, its norm integral is its integral. -/
theorem integral_norm_gaussTerm {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖gaussTerm a t n x‖) =
      1 / ((n : ℝ) + 1) -
        ((n : ℝ) + 1 + a) /
          (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  rw [← integral_gaussTerm ha t n]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ‖gaussTerm a t n x‖ = gaussTerm a t n x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact gaussTerm_nonneg ha.le t n hx.le

/-- The integrals of the norms of the Gauss summands form a summable series. -/
theorem summable_integral_norm_gaussTerm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    Summable (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ), ‖gaussTerm a t n x‖) := by
  refine (DigammaVertical.summable_re_terms ha0 ha1 t).congr fun n ↦ ?_
  exact (integral_norm_gaussTerm ha0 t n).symm

/-- Absolute integrability permits interchanging the Gauss series and its integral. -/
theorem hasSum_integral_gaussTerm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    HasSum (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ), gaussTerm a t n x)
      (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, gaussTerm a t n x) := by
  exact hasSum_integral_of_summable_integral_norm
    (fun n ↦ gaussTerm_integrableOn ha0 t n)
    (summable_integral_norm_gaussTerm ha0 ha1 t)

/-- Each Gauss summand factors into a geometric power and a fixed kernel. -/
theorem gaussTerm_eq_geometric (a t x : ℝ) (n : ℕ) :
    gaussTerm a t n x =
      Real.exp (-x) ^ n *
        (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) := by
  unfold gaussTerm
  rw [show -((n : ℝ) + 1) * x = (n : ℝ) * (-x) + (-x) by ring,
    show -((n : ℝ) + 1 + a) * x =
        (n : ℝ) * (-x) + (-(1 + a) * x) by ring,
    Real.exp_add, Real.exp_add, Real.exp_nat_mul]
  ring

/-- Pointwise geometric summation of the Gauss kernel away from the origin. -/
theorem tsum_gaussTerm (a t : ℝ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gaussTerm a t n x) =
      (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
        (1 - Real.exp (-x)) := by
  simp_rw [gaussTerm_eq_geometric]
  rw [tsum_mul_right,
    tsum_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))]
  rw [div_eq_mul_inv]
  ring

/-- The absolutely convergent vertical digamma series is the integral of the
geometrically summed Gauss kernel. -/
theorem tsum_re_terms_eq_integral_gaussKernel {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) (t : ℝ) :
    (∑' n : ℕ,
        (1 / ((n : ℝ) + 1) -
          ((n : ℝ) + 1 + a) /
            (((n : ℝ) + 1 + a) ^ 2 + t ^ 2))) =
      ∫ x in Ioi (0 : ℝ),
        (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x)) := by
  calc
    (∑' n : ℕ,
        (1 / ((n : ℝ) + 1) -
          ((n : ℝ) + 1 + a) /
            (((n : ℝ) + 1 + a) ^ 2 + t ^ 2))) =
        ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), gaussTerm a t n x := by
          apply tsum_congr
          intro n
          exact (integral_gaussTerm ha0 t n).symm
    _ = ∫ x in Ioi (0 : ℝ), ∑' n : ℕ, gaussTerm a t n x :=
      (hasSum_integral_gaussTerm ha0 ha1 t).tsum_eq
    _ = ∫ x in Ioi (0 : ℝ),
        (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact tsum_gaussTerm a t hx

/-- The pointwise sum of the Gauss summands is integrable on the positive
half-line. This records the integrability consequence needed for subsequent
linearity of the integral. -/
theorem integrableOn_tsum_gaussTerm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    IntegrableOn (fun x : ℝ ↦ ∑' n : ℕ, gaussTerm a t n x) (Ioi 0) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hFint (n : ℕ) : Integrable (gaussTerm a t n) μ :=
    gaussTerm_integrableOn ha0 t n
  have hFsum : Summable (fun n : ℕ ↦ ∫ x, ‖gaussTerm a t n x‖ ∂μ) :=
    summable_integral_norm_gaussTerm ha0 ha1 t
  constructor
  · exact AEStronglyMeasurable.tsum fun n ↦ (hFint n).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ x, ‖∑' n : ℕ, gaussTerm a t n x‖ₑ ∂μ) ≤
          ∫⁻ x, ∑' n : ℕ, ‖gaussTerm a t n x‖ₑ ∂μ :=
        lintegral_mono fun _ ↦ enorm_tsum_le_tsum_enorm
      _ = ∑' n : ℕ, ∫⁻ x, ‖gaussTerm a t n x‖ₑ ∂μ := by
        rw [lintegral_tsum]
        intro n
        exact (hFint n).aestronglyMeasurable.enorm
      _ < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        have hEq (n : ℕ) :
            (∫⁻ x, ‖gaussTerm a t n x‖ₑ ∂μ) =
              ‖∫ x, ‖gaussTerm a t n x‖ ∂μ‖ₑ := by
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hFint n)]
          rw [Real.enorm_eq_ofReal
            (integral_nonneg fun x ↦ norm_nonneg (gaussTerm a t n x))]
        rw [funext hEq]
        exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
          (NNReal.summable_coe.mp hFsum.abs)

/-- Integrability of the geometrically summed Gauss kernel. -/
theorem gaussKernel_integrableOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦
        (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x))) (Ioi 0) := by
  exact (integrableOn_tsum_gaussTerm ha0 ha1 t).congr_fun
    (fun x hx ↦ tsum_gaussTerm a t hx) measurableSet_Ioi

/-- Subtracting the first Laplace-cosine term converts the summed kernel into
Gauss' standard digamma kernel. -/
theorem gaussKernel_sub_laplace (a t : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x)) -
        Real.exp (-a * x) * Real.cos (t * x) =
      (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
        (1 - Real.exp (-x)) := by
  have hden : 1 - Real.exp (-x) ≠ 0 := by
    have hlt : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    linarith
  have hexp : Real.exp (-(1 + a) * x) = Real.exp (-a * x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp
  ring

/-- Integrability of Gauss' real digamma kernel on the positive half-line. -/
theorem digammaGaussKernel_integrableOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦
        (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x))) (Ioi 0) := by
  have hsub := (gaussKernel_integrableOn ha0 ha1 t).sub
    (integrableOn_exp_neg_mul_cos_Ioi ha0 t)
  exact hsub.congr_fun (fun x hx ↦ by
    change
      (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
            (1 - Real.exp (-x)) -
          Real.exp (-a * x) * Real.cos (t * x) =
        (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
          (1 - Real.exp (-x))
    exact gaussKernel_sub_laplace a t hx) measurableSet_Ioi

/-- Gauss' integral representation for the real part of the digamma function
on a vertical line with `0 < a < 1`. -/
theorem re_digamma_eq_gauss_integral {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re =
      -Real.eulerMascheroniConstant +
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
            (1 - Real.exp (-x)) := by
  rw [DigammaVertical.re_digamma_vertical ha0 ha1 t,
    tsum_re_terms_eq_integral_gaussKernel ha0 ha1 t]
  have hG := gaussKernel_integrableOn ha0 ha1 t
  have hE := integrableOn_exp_neg_mul_cos_Ioi ha0 t
  have hH :
      (∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
            (1 - Real.exp (-x))) =
        (∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
            (1 - Real.exp (-x))) -
        ∫ x in Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) := by
    calc
      (∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-a * x) * Real.cos (t * x)) /
            (1 - Real.exp (-x))) =
          ∫ x in Ioi (0 : ℝ),
            ((Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
                (1 - Real.exp (-x)) -
              Real.exp (-a * x) * Real.cos (t * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact (gaussKernel_sub_laplace a t hx).symm
      _ =
          (∫ x in Ioi (0 : ℝ),
            (Real.exp (-x) - Real.exp (-(1 + a) * x) * Real.cos (t * x)) /
              (1 - Real.exp (-x))) -
          ∫ x in Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) :=
        integral_sub hG hE
  rw [hH, integral_exp_neg_mul_cos_Ioi ha0 t]
  ring

/-- The real-place specialization used by the completed Dedekind zeta factor. -/
theorem re_digamma_quarter_integral (t : ℝ) :
    (Complex.digamma ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re =
      -Real.eulerMascheroniConstant +
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-(1 / 4 : ℝ) * x) *
              Real.cos ((t / 2) * x)) /
            (1 - Real.exp (-x)) := by
  simpa [mul_comm] using re_digamma_eq_gauss_integral
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (t / 2)

/-- The complex-place specialization used by the completed Dedekind zeta factor. -/
theorem re_digamma_half_integral (t : ℝ) :
    (Complex.digamma ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re =
      -Real.eulerMascheroniConstant +
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) *
              Real.cos (t * x)) /
            (1 - Real.exp (-x)) := by
  simpa [mul_comm] using re_digamma_eq_gauss_integral
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) t

/-- The symmetric archimedean logarithmic-derivative bracket with both
digamma terms replaced by their proved Gauss integrals. -/
theorem logDeriv_ZInfty_critical_bracket_integral
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
        logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) - (t : ℂ) * Complex.I) =
      Complex.log (((|NumberField.discr K| : ℤ) : ℂ)) +
        (NumberField.InfinitePlace.nrRealPlaces K : ℂ) *
          (-Complex.log (Real.pi : ℂ) +
            ((-Real.eulerMascheroniConstant +
              ∫ x in Ioi (0 : ℝ),
                (Real.exp (-x) - Real.exp (-(1 / 4 : ℝ) * x) *
                    Real.cos ((t / 2) * x)) /
                  (1 - Real.exp (-x)) : ℝ) : ℂ)) +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) *
          (-2 * Complex.log (2 * (Real.pi : ℂ)) +
            2 * ((-Real.eulerMascheroniConstant +
              ∫ x in Ioi (0 : ℝ),
                (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) *
                    Real.cos (t * x)) /
                  (1 - Real.exp (-x)) : ℝ) : ℂ)) := by
  rw [DigammaIdentities.logDeriv_ZInfty_critical_bracket,
    re_digamma_quarter_integral, re_digamma_half_integral]

end DedekindZeta.DigammaIntegral
