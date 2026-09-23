import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TraceEuclidean.V15OdlyzkoFourier

open Real Set MeasureTheory FourierTransform

namespace TraceEuclidean

noncomputable section

/-!
# The Fourier transform of the hyperbolic-secant factor

This module evaluates, in Lean, the Fourier transform of
`x ↦ 1 / cosh (x / 2)`.  The proof uses the sigmoid substitution, the complex
beta integral, and Euler's reflection formula.  It also records the analytic
hypotheses needed by the product-to-convolution step for Odlyzko's test
function.
-/

theorem v15IntegralSigmoid (g : ℝ → ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, g t) =
      ∫ x : ℝ, (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) • g (Real.sigmoid x) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.sigmoid)
    (f' := fun x : ℝ ↦ Real.sigmoid x * (1 - Real.sigmoid x))
    MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_sigmoid x).hasDerivWithinAt)
    Real.sigmoid_injective.injOn g
  rw [Set.image_univ, Real.range_sigmoid, setIntegral_univ] at h
  simpa only [abs_of_pos (mul_pos (Real.sigmoid_pos _)
    (sub_pos.mpr (Real.sigmoid_lt_one _)))] using h

theorem v15SigmoidEqExpDivCosh (x : ℝ) :
    Real.sigmoid x = Real.exp (x / 2) / (2 * Real.cosh (x / 2)) := by
  rw [Real.sigmoid_def, Real.cosh_eq]
  field_simp [Real.exp_ne_zero]
  rw [add_mul, one_mul, ← Real.exp_add]
  congr 1
  ring

theorem v15OneSubSigmoidEqExpNegDivCosh (x : ℝ) :
    1 - Real.sigmoid x = Real.exp (-x / 2) / (2 * Real.cosh (x / 2)) := by
  rw [← Real.sigmoid_neg, v15SigmoidEqExpDivCosh]
  simp only [neg_div, Real.cosh_neg]

theorem v15LogSigmoid (x : ℝ) :
    Real.log (Real.sigmoid x) = x / 2 - Real.log (2 * Real.cosh (x / 2)) := by
  rw [v15SigmoidEqExpDivCosh, Real.log_div (Real.exp_ne_zero _)
    (by positivity : (2 * Real.cosh (x / 2) : ℝ) ≠ 0), Real.log_exp]

theorem v15LogOneSubSigmoid (x : ℝ) :
    Real.log (1 - Real.sigmoid x) = -x / 2 - Real.log (2 * Real.cosh (x / 2)) := by
  rw [v15OneSubSigmoidEqExpNegDivCosh, Real.log_div (Real.exp_ne_zero _)
    (by positivity : (2 * Real.cosh (x / 2) : ℝ) ≠ 0), Real.log_exp]

private theorem v15BetaSigmoidIntegrand (k x : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) - (k : ℂ) * Complex.I
    (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) •
        ((Real.sigmoid x : ℂ) ^ (z - 1) *
          ((1 - Real.sigmoid x : ℝ) : ℂ) ^ ((1 - z) - 1)) =
      (1 / 2 : ℂ) * Complex.exp ((-(k * x) : ℝ) * Complex.I) *
        (1 / Real.cosh (x / 2) : ℝ) := by
  dsimp only
  let t : ℝ := Real.sigmoid x
  let u : ℝ := 1 - Real.sigmoid x
  have ht : 0 < t := Real.sigmoid_pos x
  have hu : 0 < u := sub_pos.mpr (Real.sigmoid_lt_one x)
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have htcombine :
      (t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) * (t : ℂ) =
        (t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I) := by
    calc
      _ = (t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) *
          (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ) ^ (((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) + 1) :=
        (Complex.cpow_add _ _ htC).symm
      _ = _ := by congr 1; ring
  have hucombine :
      (u : ℂ) ^ ((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1) * (u : ℂ) =
        (u : ℂ) ^ (1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) := by
    calc
      _ = (u : ℂ) ^ ((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1) *
          (u : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (u : ℂ) ^ (((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1) + 1) :=
        (Complex.cpow_add _ _ huC).symm
      _ = _ := by congr 1; ring
  change ((t * u : ℝ) : ℂ) *
      ((t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) *
        (u : ℂ) ^ ((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1)) = _
  rw [Complex.ofReal_mul]
  calc
    (t : ℂ) * (u : ℂ) *
        ((t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) *
          (u : ℂ) ^ ((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1)) =
        ((t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I - 1) * (t : ℂ)) *
          ((u : ℂ) ^ ((1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) - 1) * (u : ℂ)) := by
            ring
    _ = (t : ℂ) ^ ((1 / 2 : ℂ) - (k : ℂ) * Complex.I) *
          (u : ℂ) ^ (1 - ((1 / 2 : ℂ) - (k : ℂ) * Complex.I)) := by
      rw [htcombine, hucombine]
    _ = Complex.exp
          (-(Real.log (2 * Real.cosh (x / 2)) : ℂ) - (k * x : ℝ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero htC, Complex.cpow_def_of_ne_zero huC,
        ← Complex.exp_add, ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hu.le]
      congr 1
      rw [show t = Real.sigmoid x by rfl, show u = 1 - Real.sigmoid x by rfl,
        v15LogSigmoid, v15LogOneSubSigmoid]
      push_cast
      ring
    _ = (1 / 2 : ℂ) * Complex.exp ((-(k * x) : ℝ) * Complex.I) *
          (1 / Real.cosh (x / 2) : ℝ) := by
      rw [Complex.exp_sub, Complex.exp_neg, ← Complex.ofReal_exp,
        Real.exp_log (by positivity : 0 < 2 * Real.cosh (x / 2)),
        div_eq_mul_inv, ← Complex.exp_neg]
      push_cast
      field_simp [Real.cosh_pos (x / 2) |>.ne']

theorem v15BetaIntegralEqIntegralIoo (z : ℂ) :
    Complex.betaIntegral z (1 - z) =
      ∫ t : ℝ in Ioo 0 1,
        (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ ((1 - z) - 1) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume)).symm

private theorem v15OdlyzkoExpNegAbsIntegrable :
    Integrable (fun x : ℝ ↦ 2 * Real.exp (-|x| / 2)) volume := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have h : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp ((1 / 2 : ℝ) * x)) (Iic 0) volume :=
      (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul 2
    refine h.congr_fun ?_ measurableSet_Iic
    intro x hx
    change 2 * Real.exp ((1 / 2 : ℝ) * x) = 2 * Real.exp (-|x| / 2)
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  · have h : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp ((-1 / 2 : ℝ) * x)) (Ioi 0) volume :=
      (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) 0).const_mul 2
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change 2 * Real.exp ((-1 / 2 : ℝ) * x) = 2 * Real.exp (-|x| / 2)
    rw [abs_of_nonneg (show 0 ≤ x from hx.le)]
    congr 1
    ring

/-- The real hyperbolic-secant factor in Odlyzko's test function. -/
def v15OdlyzkoSech (x : ℝ) : ℝ := 1 / Real.cosh (x / 2)

theorem v15OdlyzkoSech_continuous : Continuous v15OdlyzkoSech := by
  exact continuous_const.div (continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

theorem v15OdlyzkoSech_integrable : Integrable v15OdlyzkoSech volume := by
  apply Integrable.mono' v15OdlyzkoExpNegAbsIntegrable
  · exact v15OdlyzkoSech_continuous.aestronglyMeasurable
  · filter_upwards with x
    have hcosh : Real.exp (|x| / 2) / 2 ≤ Real.cosh (x / 2) := by
      rw [Real.cosh_eq]
      have h := Real.exp_abs_le (x / 2)
      rw [abs_div] at h
      norm_num at h ⊢
      linarith
    have hinv := one_div_le_one_div_of_le
      (by positivity : 0 < Real.exp (|x| / 2) / 2) hcosh
    calc
      ‖v15OdlyzkoSech x‖ = 1 / Real.cosh (x / 2) := by
        rw [v15OdlyzkoSech, Real.norm_eq_abs,
          abs_of_pos (one_div_pos.mpr (Real.cosh_pos (x / 2)))]
      _ ≤ 1 / (Real.exp (|x| / 2) / 2) := hinv
      _ = 2 * Real.exp (-|x| / 2) := by
        rw [show -|x| / 2 = -(|x| / 2) by ring, Real.exp_neg]
        field_simp [Real.exp_ne_zero]

/-- The complex-valued version of the hyperbolic-secant factor. -/
def v15OdlyzkoSechComplex (x : ℝ) : ℂ := v15OdlyzkoSech x

theorem v15OdlyzkoSechComplex_continuous : Continuous v15OdlyzkoSechComplex := by
  change Continuous (Complex.ofReal ∘ v15OdlyzkoSech)
  exact Complex.continuous_ofReal.comp v15OdlyzkoSech_continuous

theorem v15OdlyzkoSechComplex_integrable :
    Integrable v15OdlyzkoSechComplex volume := by
  exact v15OdlyzkoSech_integrable.ofReal

theorem v15OdlyzkoSechFourierEqBeta (w : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
    𝓕 v15OdlyzkoSechComplex w = 2 * Complex.betaIntegral z (1 - z) := by
  dsimp only
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [v15OdlyzkoSechComplex, smul_eq_mul]
  let z : ℂ := (1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
  let g : ℝ → ℂ := fun t ↦
    (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ ((1 - z) - 1)
  have hbeta : Complex.betaIntegral z (1 - z) =
      ∫ x : ℝ, (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) • g (Real.sigmoid x) :=
    (v15BetaIntegralEqIntegralIoo z).trans (v15IntegralSigmoid g)
  have hpoint (x : ℝ) :
      (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) • g (Real.sigmoid x) =
        (1 / 2 : ℂ) *
          (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
            (1 / Real.cosh (x / 2) : ℝ)) := by
    dsimp only [g, z]
    convert v15BetaSigmoidIntegrand (2 * Real.pi * w) x using 1 <;> push_cast <;> ring
  simp_rw [hpoint, MeasureTheory.integral_const_mul] at hbeta
  calc
    (∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
        ↑(1 / Real.cosh (x / 2))) =
        2 * ((1 / 2 : ℂ) *
          ∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
            ↑(1 / Real.cosh (x / 2))) := by ring
    _ = 2 * Complex.betaIntegral z (1 - z) := by rw [← hbeta]

theorem v15SinReflectionArgument (w : ℝ) :
    Complex.sin ((Real.pi : ℂ) *
      ((1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I)) =
      (Real.cosh (2 * Real.pi ^ 2 * w) : ℂ) := by
  have harg :
      (Real.pi : ℂ) * ((1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I) =
        (Real.pi : ℂ) / 2 - (2 * Real.pi ^ 2 * w : ℝ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.sin_pi_div_two_sub, Complex.cos_mul_I,
    ← Complex.ofReal_cosh]

theorem v15BetaReflectionCosh (w : ℝ) :
    let z : ℂ := (1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
    Complex.betaIntegral z (1 - z) =
      (Real.pi : ℂ) / (Real.cosh (2 * Real.pi ^ 2 * w) : ℝ) := by
  dsimp only
  let z : ℂ := (1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
  have hz : 0 < z.re := by
    dsimp only [z]
    norm_num
  have h1z : 0 < (1 - z).re := by
    dsimp only [z]
    norm_num
  rw [Complex.betaIntegral_eq_Gamma_mul_div z (1 - z) hz h1z]
  have hsum : z + (1 - z) = 1 := by ring
  rw [hsum, Complex.Gamma_one, div_one, Complex.Gamma_mul_Gamma_one_sub]
  rw [show z = (1 / 2 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I by rfl,
    v15SinReflectionArgument]

theorem v15OdlyzkoSechFourier (w : ℝ) :
    𝓕 v15OdlyzkoSechComplex w =
      ((2 * Real.pi / Real.cosh (2 * Real.pi ^ 2 * w) : ℝ) : ℂ) := by
  rw [v15OdlyzkoSechFourierEqBeta, v15BetaReflectionCosh]
  push_cast
  ring

theorem v15OdlyzkoSechFourierRePos (w : ℝ) :
    0 < (𝓕 v15OdlyzkoSechComplex w).re := by
  rw [v15OdlyzkoSechFourier]
  simp only [Complex.ofReal_re]
  exact div_pos (mul_pos two_pos Real.pi_pos) (Real.cosh_pos _)

theorem v15OdlyzkoSechFourierImEqZero (w : ℝ) :
    (𝓕 v15OdlyzkoSechComplex w).im = 0 := by
  rw [v15OdlyzkoSechFourier]
  exact Complex.ofReal_im _

theorem v15OdlyzkoSechFourier_integrable :
    Integrable (𝓕 v15OdlyzkoSechComplex) volume := by
  have hscale : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hreal : Integrable
      (fun w : ℝ ↦ 2 * Real.pi * v15OdlyzkoSech ((4 * Real.pi ^ 2) * w)) volume :=
    (v15OdlyzkoSech_integrable.comp_mul_left' hscale).const_mul (2 * Real.pi)
  have hcomplex : Integrable
      (fun w : ℝ ↦ ((2 * Real.pi *
        v15OdlyzkoSech ((4 * Real.pi ^ 2) * w) : ℝ) : ℂ)) volume :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards with w
  rw [v15OdlyzkoSechFourier]
  simp only [v15OdlyzkoSech]
  push_cast
  congr 2
  ring

end
end TraceEuclidean
