import TraceEuclidean.V15OdlyzkoSechFourier

open Real Set MeasureTheory FourierTransform

namespace TraceEuclidean

noncomputable section

/-!
# The hyperbolic-secant factor away from the critical line

The real Fourier transform of the complete test function only controls the
central line.  For the unconditional explicit formula, the zero term also
requires control when the real part of the zero varies across the critical
strip.  This module begins that bridge by evaluating the exponentially
tilted hyperbolic-secant factor.
-/

/-- The exponentially tilted hyperbolic-secant factor. -/
def v15OdlyzkoTiltedSech (a x : ℝ) : ℂ :=
  ((Real.exp (a * x) / Real.cosh (x / 2) : ℝ) : ℂ)

theorem v15OdlyzkoTiltedSech_continuous (a : ℝ) :
    Continuous (v15OdlyzkoTiltedSech a) := by
  change Continuous (Complex.ofReal ∘
    fun x : ℝ ↦ Real.exp (a * x) / Real.cosh (x / 2))
  apply Complex.continuous_ofReal.comp
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne'))

private theorem v15TiltedEnvelope_integrable (a : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (fun x : ℝ ↦ 2 * Real.exp (a * x - |x| / 2)) volume := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have h : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp ((a + 1 / 2) * x))
        (Iic 0) volume :=
      (integrableOn_exp_mul_Iic (a := a + 1 / 2) (by linarith) 0).const_mul 2
    refine h.congr_fun ?_ measurableSet_Iic
    intro x hx
    change 2 * Real.exp ((a + 1 / 2) * x) =
      2 * Real.exp (a * x - |x| / 2)
    rw [abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    ring
  · have h : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp ((a - 1 / 2) * x))
        (Ioi 0) volume :=
      (integrableOn_exp_mul_Ioi (a := a - 1 / 2) (by linarith) 0).const_mul 2
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change 2 * Real.exp ((a - 1 / 2) * x) =
      2 * Real.exp (a * x - |x| / 2)
    rw [abs_of_nonneg (show 0 ≤ x from hx.le)]
    congr 1
    ring

/-- The tilted factor is integrable for every weight in the open strip. -/
theorem v15OdlyzkoTiltedSech_integrable (a : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (v15OdlyzkoTiltedSech a) volume := by
  apply Integrable.mono' (v15TiltedEnvelope_integrable a ha₁ ha₂)
  · exact (v15OdlyzkoTiltedSech_continuous a).aestronglyMeasurable
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
      ‖v15OdlyzkoTiltedSech a x‖ =
          Real.exp (a * x) / Real.cosh (x / 2) := by
        rw [v15OdlyzkoTiltedSech, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]
      _ = Real.exp (a * x) * (1 / Real.cosh (x / 2)) := by ring
      _ ≤ Real.exp (a * x) * (1 / (Real.exp (|x| / 2) / 2)) :=
        mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
      _ = 2 * Real.exp (a * x - |x| / 2) := by
        rw [Real.exp_sub]
        field_simp [Real.exp_ne_zero]

private theorem v15BetaTiltedSigmoidIntegrand (a k x : ℝ) :
    let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I
    (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) •
        ((Real.sigmoid x : ℂ) ^ (z - 1) *
          ((1 - Real.sigmoid x : ℝ) : ℂ) ^ ((1 - z) - 1)) =
      (1 / 2 : ℂ) * Complex.exp
        (((a * x : ℝ) : ℂ) - (k * x : ℝ) * Complex.I) *
          (1 / Real.cosh (x / 2) : ℝ) := by
  dsimp only
  let t : ℝ := Real.sigmoid x
  let u : ℝ := 1 - Real.sigmoid x
  have ht : 0 < t := Real.sigmoid_pos x
  have hu : 0 < u := sub_pos.mpr (Real.sigmoid_lt_one x)
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have htcombine :
      (t : ℂ) ^ (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I - 1) * (t : ℂ) =
        (t : ℂ) ^ (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I) := by
    calc
      _ = (t : ℂ) ^ (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I - 1) *
          (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ) ^
          ((((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I - 1) + 1) :=
        (Complex.cpow_add _ _ htC).symm
      _ = _ := by congr 1; ring
  have hucombine :
      (u : ℂ) ^ ((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1) *
          (u : ℂ) =
        (u : ℂ) ^ (1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) := by
    calc
      _ = (u : ℂ) ^
          ((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1) *
          (u : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (u : ℂ) ^
          (((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1) + 1) :=
        (Complex.cpow_add _ _ huC).symm
      _ = _ := by congr 1; ring
  change ((t * u : ℝ) : ℂ) *
      ((t : ℂ) ^ ((((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I) - 1) *
        (u : ℂ) ^ ((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1)) = _
  rw [Complex.ofReal_mul]
  calc
    (t : ℂ) * (u : ℂ) *
        ((t : ℂ) ^ ((((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I) - 1) *
          (u : ℂ) ^ ((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1)) =
        ((t : ℂ) ^ ((((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I) - 1) *
          (t : ℂ)) *
          ((u : ℂ) ^ ((1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) - 1) *
            (u : ℂ)) := by ring
    _ = (t : ℂ) ^ (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I) *
        (u : ℂ) ^ (1 - (((1 / 2 + a : ℝ) : ℂ) - (k : ℂ) * Complex.I)) := by
      rw [htcombine, hucombine]
    _ = Complex.exp
          (((a * x : ℝ) : ℂ) -
            (Real.log (2 * Real.cosh (x / 2)) : ℂ) -
            (k * x : ℝ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero htC, Complex.cpow_def_of_ne_zero huC,
        ← Complex.exp_add, ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hu.le]
      congr 1
      rw [show t = Real.sigmoid x by rfl, show u = 1 - Real.sigmoid x by rfl,
        v15LogSigmoid, v15LogOneSubSigmoid]
      push_cast
      ring
    _ = (1 / 2 : ℂ) * Complex.exp
          (((a * x : ℝ) : ℂ) - (k * x : ℝ) * Complex.I) *
            (1 / Real.cosh (x / 2) : ℝ) := by
      rw [show ((a * x : ℝ) : ℂ) -
          (Real.log (2 * Real.cosh (x / 2)) : ℂ) -
          (k * x : ℝ) * Complex.I =
          (((a * x : ℝ) : ℂ) - (k * x : ℝ) * Complex.I) -
          (Real.log (2 * Real.cosh (x / 2)) : ℂ) by ring,
        Complex.exp_sub, ← Complex.ofReal_exp,
        Real.exp_log (by positivity : 0 < 2 * Real.cosh (x / 2)),
        div_eq_mul_inv]
      push_cast
      field_simp [Real.cosh_pos (x / 2) |>.ne']

/-- The beta-integral evaluation of the tilted hyperbolic-secant transform. -/
theorem v15OdlyzkoTiltedSech_fourier_eq_beta (a w : ℝ) :
    let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) -
      (2 * Real.pi * w : ℝ) * Complex.I
    𝓕 (v15OdlyzkoTiltedSech a) w =
      2 * Complex.betaIntegral z (1 - z) := by
  dsimp only
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) -
    (2 * Real.pi * w : ℝ) * Complex.I
  let g : ℝ → ℂ := fun t ↦
    (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ ((1 - z) - 1)
  have hbeta : Complex.betaIntegral z (1 - z) =
      ∫ x : ℝ, (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) •
        g (Real.sigmoid x) :=
    (v15BetaIntegralEqIntegralIoo z).trans (v15IntegralSigmoid g)
  have hpoint (x : ℝ) :
      (Real.sigmoid x * (1 - Real.sigmoid x) : ℝ) • g (Real.sigmoid x) =
        (1 / 2 : ℂ) *
          (Complex.exp (((a * x : ℝ) : ℂ) -
            (2 * Real.pi * x * w : ℝ) * Complex.I) *
              (1 / Real.cosh (x / 2) : ℝ)) := by
    dsimp only [g, z]
    convert v15BetaTiltedSigmoidIntegrand a (2 * Real.pi * w) x using 1 <;>
      push_cast <;> ring
  simp_rw [hpoint, MeasureTheory.integral_const_mul] at hbeta
  calc
    (∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
        v15OdlyzkoTiltedSech a x) =
        2 * ((1 / 2 : ℂ) *
          ∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
            v15OdlyzkoTiltedSech a x) := by ring
    _ = 2 * Complex.betaIntegral z (1 - z) := by
      rw [hbeta]
      congr 2
      apply integral_congr_ae
      filter_upwards with x
      simp only [v15OdlyzkoTiltedSech, Complex.ofReal_div]
      rw [Complex.exp_sub, ← Complex.ofReal_exp]
      have harg :
          ((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I =
            -(((2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [harg, Complex.exp_neg]
      push_cast
      ring

private theorem v15TiltedReflectionSinRe (a w : ℝ) :
    (Complex.sin ((Real.pi : ℂ) *
      (((1 / 2 + a : ℝ) : ℂ) -
        (2 * Real.pi * w : ℝ) * Complex.I))).re =
      Real.cos (Real.pi * a) * Real.cosh (2 * Real.pi ^ 2 * w) := by
  have harg :
      (Real.pi : ℂ) *
          (((1 / 2 + a : ℝ) : ℂ) -
            (2 * Real.pi * w : ℝ) * Complex.I) =
        ((Real.pi : ℂ) * (a : ℂ) -
          (2 * Real.pi ^ 2 * w : ℝ) * Complex.I) +
          (Real.pi : ℂ) / 2 := by
    push_cast
    ring
  rw [harg, Complex.sin_add_pi_div_two, Complex.cos_sub,
    Complex.cos_mul_I, Complex.sin_mul_I]
  norm_num [Complex.add_re, Complex.mul_re, ← Complex.ofReal_mul,
    ← Complex.ofReal_pow]
  exact Or.inl (Complex.cos_ofReal_re _)

private theorem v15TiltedReflectionSinRePos (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    0 < (Complex.sin ((Real.pi : ℂ) *
      (((1 / 2 + a : ℝ) : ℂ) -
        (2 * Real.pi * w : ℝ) * Complex.I))).re := by
  rw [v15TiltedReflectionSinRe]
  apply mul_pos _ (Real.cosh_pos _)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h := mul_lt_mul_of_pos_left ha₁ Real.pi_pos
    nlinarith
  · have h := mul_lt_mul_of_pos_left ha₂ Real.pi_pos
    nlinarith

/-- Exact transform in the open critical strip, expressed by Euler's
reflection formula. -/
theorem v15OdlyzkoTiltedSech_fourier_eq_sin (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) -
      (2 * Real.pi * w : ℝ) * Complex.I
    𝓕 (v15OdlyzkoTiltedSech a) w =
      2 * (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by
  dsimp only
  rw [v15OdlyzkoTiltedSech_fourier_eq_beta]
  let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) -
    (2 * Real.pi * w : ℝ) * Complex.I
  have hz : 0 < z.re := by
    dsimp only [z]
    norm_num
    linarith
  have h1z : 0 < (1 - z).re := by
    dsimp only [z]
    norm_num
    linarith
  rw [Complex.betaIntegral_eq_Gamma_mul_div z (1 - z) hz h1z]
  have hsum : z + (1 - z) = 1 := by ring
  rw [hsum, Complex.Gamma_one, div_one, Complex.Gamma_mul_Gamma_one_sub]
  ring

/-- The tilted factor has strictly positive real Fourier transform throughout
the open critical strip. -/
theorem v15OdlyzkoTiltedSech_fourier_re_pos (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    0 < (𝓕 (v15OdlyzkoTiltedSech a) w).re := by
  rw [v15OdlyzkoTiltedSech_fourier_eq_sin a w ha₁ ha₂, Complex.div_re]
  have hre : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by norm_num
  have him : (2 * (Real.pi : ℂ)).im = 0 := by norm_num
  rw [hre, him]
  simp only [zero_mul, zero_div, add_zero]
  have hden := v15TiltedReflectionSinRePos a w ha₁ ha₂
  have hnonzero : Complex.sin ((Real.pi : ℂ) *
      (((1 / 2 + a : ℝ) : ℂ) -
        (2 * Real.pi * w : ℝ) * Complex.I)) ≠ 0 := by
    intro h
    rw [h] at hden
    simp at hden
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hden)
    (Complex.normSq_pos.mpr hnonzero)

private theorem v15TiltedCosPos (a : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    0 < Real.cos (Real.pi * a) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h := mul_lt_mul_of_pos_left ha₁ Real.pi_pos
    nlinarith
  · have h := mul_lt_mul_of_pos_left ha₂ Real.pi_pos
    nlinarith

private theorem v15TiltedSechFourierNormBound (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    ‖𝓕 (v15OdlyzkoTiltedSech a) w‖ ≤
      (2 * Real.pi / Real.cos (Real.pi * a)) *
        v15OdlyzkoSech ((4 * Real.pi ^ 2) * w) := by
  let z : ℂ := ((1 / 2 + a : ℝ) : ℂ) -
    (2 * Real.pi * w : ℝ) * Complex.I
  have hcos := v15TiltedCosPos a ha₁ ha₂
  have hden : 0 < Real.cos (Real.pi * a) *
      Real.cosh (2 * Real.pi ^ 2 * w) :=
    mul_pos hcos (Real.cosh_pos _)
  have hle : Real.cos (Real.pi * a) *
      Real.cosh (2 * Real.pi ^ 2 * w) ≤
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    exact (v15TiltedReflectionSinRe a w).symm ▸
      Complex.re_le_norm _
  calc
    ‖𝓕 (v15OdlyzkoTiltedSech a) w‖ =
        (2 * Real.pi) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [v15OdlyzkoTiltedSech_fourier_eq_sin a w ha₁ ha₂]
      simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
      dsimp only [z]
      congr 3
      push_cast
      ring
    _ ≤ (2 * Real.pi) /
          (Real.cos (Real.pi * a) * Real.cosh (2 * Real.pi ^ 2 * w)) :=
      div_le_div_of_nonneg_left (by positivity) hden hle
    _ = (2 * Real.pi / Real.cos (Real.pi * a)) *
          v15OdlyzkoSech ((4 * Real.pi ^ 2) * w) := by
      rw [v15OdlyzkoSech]
      have hcosh : Real.cosh (2 * Real.pi ^ 2 * w) ≠ 0 :=
        (Real.cosh_pos _).ne'
      field_simp [hcos.ne', hcosh]
      congr 1
      ring

/-- The tilted factor's Fourier transform is integrable for every weight in
the open strip.  This permits Fourier inversion in the product argument. -/
theorem v15OdlyzkoTiltedSech_fourier_integrable (a : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (𝓕 (v15OdlyzkoTiltedSech a)) volume := by
  have hscale : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hbound : Integrable (fun w : ℝ ↦
      (2 * Real.pi / Real.cos (Real.pi * a)) *
        v15OdlyzkoSech ((4 * Real.pi ^ 2) * w)) volume :=
    (v15OdlyzkoSech_integrable.comp_mul_left' hscale).const_mul _
  apply Integrable.mono' hbound
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂
      (v15OdlyzkoTiltedSech_integrable a ha₁ ha₂)).aestronglyMeasurable
  · filter_upwards with w
    exact v15TiltedSechFourierNormBound a w ha₁ ha₂

end
end TraceEuclidean
