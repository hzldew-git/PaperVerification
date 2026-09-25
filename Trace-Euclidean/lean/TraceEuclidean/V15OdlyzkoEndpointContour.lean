import TraceEuclidean.Analytic.RectangleLogDeriv
import TraceEuclidean.V15OdlyzkoArchimedeanShift
import TraceEuclidean.V15OdlyzkoContourFinite
import TraceEuclidean.V15OdlyzkoPhiEndpoint
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The two elementary endpoint terms in the Odlyzko contour

The pole-removal factor in the completed Dedekind zeta is the polynomial
`s (s - 1)`.  Its logarithmic derivative has one simple pole at each of
`0` and `1`.  The weighted argument principle therefore evaluates its
finite rectangular contour as `Phi 0 + Phi 1`.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

/-- The elementary polynomial that removes the two completed-zeta poles. -/
def v15OdlyzkoEndpointPolynomial (s : ℂ) : ℂ :=
  s * (s - 1)

/-- The corresponding weighted logarithmic-derivative integrand. -/
def v15OdlyzkoEndpointIntegrand (s : ℂ) : ℂ :=
  v15OdlyzkoPhi s * logDeriv v15OdlyzkoEndpointPolynomial s

lemma v15OdlyzkoEndpointPolynomial_analyticOnNhd :
    AnalyticOnNhd ℂ v15OdlyzkoEndpointPolynomial Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro s
  exact differentiableAt_id.mul
    (differentiableAt_id.sub (differentiableAt_const 1))

lemma v15OdlyzkoPhi_analyticOnNhd :
    AnalyticOnNhd ℂ v15OdlyzkoPhi Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  exact v15OdlyzkoPhi_differentiable

lemma v15OdlyzkoEndpointPolynomial_eq_zero_iff (s : ℂ) :
    v15OdlyzkoEndpointPolynomial s = 0 ↔ s = 0 ∨ s = 1 := by
  rw [v15OdlyzkoEndpointPolynomial, mul_eq_zero, sub_eq_zero]

lemma v15OdlyzkoEndpointPolynomial_deriv (s : ℂ) :
    deriv v15OdlyzkoEndpointPolynomial s = 2 * s - 1 := by
  change deriv (fun z : ℂ ↦ z * (z - 1)) s = 2 * s - 1
  calc
    _ = 1 * (s - 1) + s * 1 :=
      ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).deriv
    _ = _ := by ring

lemma v15OdlyzkoEndpointPolynomial_order_zero :
    analyticOrderNatAt v15OdlyzkoEndpointPolynomial 0 = 1 := by
  have hAnalytic : AnalyticAt ℂ v15OdlyzkoEndpointPolynomial 0 :=
    v15OdlyzkoEndpointPolynomial_analyticOnNhd 0 (mem_univ 0)
  have hOrder := hAnalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (by simp [v15OdlyzkoEndpointPolynomial])
    (by rw [v15OdlyzkoEndpointPolynomial_deriv]; norm_num)
  simp [analyticOrderNatAt, hOrder]

lemma v15OdlyzkoEndpointPolynomial_order_one :
    analyticOrderNatAt v15OdlyzkoEndpointPolynomial 1 = 1 := by
  have hAnalytic : AnalyticAt ℂ v15OdlyzkoEndpointPolynomial 1 :=
    v15OdlyzkoEndpointPolynomial_analyticOnNhd 1 (mem_univ 1)
  have hOrder := hAnalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (by simp [v15OdlyzkoEndpointPolynomial])
    (by rw [v15OdlyzkoEndpointPolynomial_deriv]; norm_num)
  simp [analyticOrderNatAt, hOrder]

/-- The endpoint polynomial is nonzero on the boundary of every symmetric
rectangle of positive height. -/
lemma v15OdlyzkoEndpointPolynomial_ne_zero_on_border
    {R : ℝ} (hR : 0 < R) (s : ℂ)
    (hs : s ∈ RectangleBorder (v15OdlyzkoContourLower 2 R)
      (v15OdlyzkoContourUpper 2 R)) :
    v15OdlyzkoEndpointPolynomial s ≠ 0 := by
  have hzeroNot : (0 : ℂ) ∉ RectangleBorder
      (v15OdlyzkoContourLower 2 R) (v15OdlyzkoContourUpper 2 R) := by
    exact Set.disjoint_right.mp
      (rectangleBorder_disjoint_singleton (p := (0 : ℂ)) (by
        norm_num [v15OdlyzkoContourLower, v15OdlyzkoContourUpper,
          hR.ne, hR.ne'])) rfl
  have honeNot : (1 : ℂ) ∉ RectangleBorder
      (v15OdlyzkoContourLower 2 R) (v15OdlyzkoContourUpper 2 R) := by
    exact Set.disjoint_right.mp
      (rectangleBorder_disjoint_singleton (p := (1 : ℂ)) (by
        norm_num [v15OdlyzkoContourLower, v15OdlyzkoContourUpper,
          hR.ne, hR.ne'])) rfl
  intro h
  rcases (v15OdlyzkoEndpointPolynomial_eq_zero_iff s).mp h with rfl | rfl
  · exact hzeroNot hs
  · exact honeNot hs

/-- The finite normalized endpoint contour is exactly the sum of the two
endpoint transform values. -/
theorem v15OdlyzkoEndpoint_rectangleIntegral
    {R : ℝ} (hR : 0 < R) :
    RectangleIntegral' v15OdlyzkoEndpointIntegrand
        (v15OdlyzkoContourLower 2 R) (v15OdlyzkoContourUpper 2 R) =
      v15OdlyzkoPhi 0 + v15OdlyzkoPhi 1 := by
  let z := v15OdlyzkoContourLower 2 R
  let w := v15OdlyzkoContourUpper 2 R
  have hre : z.re ≤ w.re := by
    dsimp [z, w, v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    norm_num [Complex.mul_re]
  have him : z.im ≤ w.im := by
    dsimp [z, w, v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    simp only [ofReal_im, mul_im, I_im, ofReal_re, mul_one,
      zero_sub, zero_add]
    linarith
  have hzeroMem : (0 : ℂ) ∈ Rectangle z w := by
    rw [mem_Rect hre him]
    dsimp [z, w, v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    norm_num
    exact hR.le
  have honeMem : (1 : ℂ) ∈ Rectangle z w := by
    rw [mem_Rect hre him]
    dsimp [z, w, v15OdlyzkoContourLower, v15OdlyzkoContourUpper]
    norm_num
    exact hR.le
  have hArgument := Analytic.rectangleIntegral'_mul_logDeriv
    (f := v15OdlyzkoEndpointPolynomial) (g := v15OdlyzkoPhi)
    (z := z) (w := w) hre him
    (v15OdlyzkoEndpointPolynomial_analyticOnNhd.mono (subset_univ _))
    (v15OdlyzkoPhi_analyticOnNhd.mono (subset_univ _))
    (fun s hs ↦ v15OdlyzkoEndpointPolynomial_ne_zero_on_border hR s (by simpa [z, w] using hs))
    ({0, 1} : Finset ℂ)
    (fun s _ ↦ by simp [v15OdlyzkoEndpointPolynomial_eq_zero_iff])
    (by simpa using insert_subset hzeroMem (singleton_subset_iff.mpr honeMem))
  change RectangleIntegral'
      (fun s ↦ v15OdlyzkoPhi s * logDeriv v15OdlyzkoEndpointPolynomial s)
      z w = _
  rw [hArgument]
  simp [v15OdlyzkoEndpointPolynomial_order_zero,
    v15OdlyzkoEndpointPolynomial_order_one]

/-- Away from its two zeros, the logarithmic derivative of `s (s - 1)` is
the sum of the two elementary fractions. -/
lemma v15OdlyzkoEndpointPolynomial_logDeriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv v15OdlyzkoEndpointPolynomial s =
      1 / s + 1 / (s - 1) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul := logDeriv_mul
    (f := fun u : ℂ ↦ u) (g := fun u : ℂ ↦ u - 1) s
    hs0 hsub differentiableAt_id
      (differentiableAt_id.sub (differentiableAt_const 1))
  change logDeriv (fun u : ℂ ↦ u * (u - 1)) s = _
  rw [hmul, logDeriv_id']
  simp only [logDeriv_apply]
  have hderiv : deriv (fun u : ℂ ↦ u - 1) s = 1 := by
    simpa using ((hasDerivAt_id s).sub_const 1).deriv
  rw [hderiv]

/-- The endpoint integrand is odd under reflection about the center of the
critical strip, away from the two endpoints. -/
lemma v15OdlyzkoEndpointIntegrand_one_sub
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    v15OdlyzkoEndpointIntegrand (1 - s) =
      -v15OdlyzkoEndpointIntegrand s := by
  have hOneSub0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hOneSub1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  rw [v15OdlyzkoEndpointIntegrand, v15OdlyzkoEndpointIntegrand,
    v15OdlyzkoPhi_one_sub,
    v15OdlyzkoEndpointPolynomial_logDeriv hOneSub0 hOneSub1,
    v15OdlyzkoEndpointPolynomial_logDeriv hs0 hs1]
  field_simp [hs0, hs1]
  ring

/-- The elementary endpoint integrand is absolutely integrable on the right
vertical line. -/
theorem v15OdlyzkoEndpointIntegrand_right_vertical_integrable :
    Integrable (fun t : ℝ ↦ v15OdlyzkoEndpointIntegrand
      ((2 : ℂ) + (t : ℂ) * I)) volume := by
  obtain ⟨D, hD, hPhi⟩ :=
    v15OdlyzkoPhi_exists_wideFourthPowerBound
  let line : ℝ → ℂ := fun t ↦ (2 : ℂ) + (t : ℂ) * I
  have hline : Continuous line := by fun_prop
  have hline0 : ∀ t : ℝ, line t ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    norm_num [line] at hre
  have hline1 : ∀ t : ℝ, line t - 1 ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    norm_num [line] at hre
  have hExplicit : ∀ t : ℝ,
      v15OdlyzkoEndpointIntegrand (line t) =
        v15OdlyzkoPhi (line t) *
          (1 / line t + 1 / (line t - 1)) := by
    intro t
    rw [v15OdlyzkoEndpointIntegrand,
      v15OdlyzkoEndpointPolynomial_logDeriv (hline0 t)
        (sub_ne_zero.mp (hline1 t))]
  have hcont : Continuous (fun t : ℝ ↦
      v15OdlyzkoPhi (line t) *
        (1 / line t + 1 / (line t - 1))) := by
    exact (v15OdlyzkoPhi_differentiable.continuous.comp hline).mul
      ((continuous_const.div hline hline0).add
        (continuous_const.div (hline.sub continuous_const) hline1))
  apply (v15OdlyzkoCriticalMajorant_integrable (2 * D)).mono'
  · exact hcont.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun t ↦ (hExplicit t).symm)
  · filter_upwards with t
    let u : ℝ := 1 + |t|
    have hu : 0 < u := by dsimp only [u]; positivity
    have hPhi' : ‖v15OdlyzkoPhi (line t)‖ ≤ D / u ^ 4 := by
      simpa [line, u] using hPhi (line t)
        (by norm_num [line]) (by norm_num [line])
    have hnorm0 : 1 ≤ ‖line t‖ := by
      calc
        1 ≤ |(line t).re| := by simp [line]
        _ ≤ ‖line t‖ := Complex.abs_re_le_norm _
    have hnorm1 : 1 ≤ ‖line t - 1‖ := by
      calc
        1 ≤ |(line t - 1).re| := by norm_num [line]
        _ ≤ ‖line t - 1‖ := Complex.abs_re_le_norm _
    have hinv0 : ‖1 / line t‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr (hline0 t))]
      simpa using hnorm0
    have hinv1 : ‖1 / (line t - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr (hline1 t))]
      simpa using hnorm1
    rw [hExplicit t, norm_mul]
    have hfrac : ‖1 / line t + 1 / (line t - 1)‖ ≤ 2 := by
      linarith [norm_add_le (1 / line t) (1 / (line t - 1))]
    calc
      ‖v15OdlyzkoPhi (line t)‖ *
          ‖1 / line t + 1 / (line t - 1)‖ ≤ (D / u ^ 4) * 2 :=
        mul_le_mul hPhi' hfrac (norm_nonneg _)
          (div_nonneg hD (pow_nonneg hu.le 4))
      _ = 2 * D / u ^ 4 := by ring

/-- Symmetric truncations of the endpoint right-line integral converge to
the full-line integral. -/
theorem v15OdlyzkoEndpointIntegrand_right_vertical_tendsto :
    Tendsto (fun n : ℕ ↦ ∫ t in (-((n : ℝ) + 1))..((n : ℝ) + 1),
      v15OdlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, v15OdlyzkoEndpointIntegrand
        ((2 : ℂ) + (t : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    v15OdlyzkoEndpointIntegrand_right_vertical_integrable
    (tendsto_neg_atTop_atBot.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Folding the left endpoint vertical side onto the right one. -/
theorem v15OdlyzkoEndpointIntegrand_verticals_eq (R : ℝ) :
    VIntegral v15OdlyzkoEndpointIntegrand 2 (-R) R -
        VIntegral v15OdlyzkoEndpointIntegrand (-1) (-R) R =
      I • ∫ t in (-R)..R,
        2 * v15OdlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I) := by
  have hleft : ∀ y : ℝ,
      v15OdlyzkoEndpointIntegrand ((-1 : ℂ) + (y : ℂ) * I) =
        -v15OdlyzkoEndpointIntegrand
          ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    intro y
    let s : ℂ := (2 : ℂ) + ((-y : ℝ) : ℂ) * I
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    have hreflect :
        ((-1 : ℂ) + (y : ℂ) * I) = 1 - s := by
      dsimp only [s]
      push_cast
      ring
    rw [hreflect, v15OdlyzkoEndpointIntegrand_one_sub hs0 hs1]
  have hfold :
      (∫ y in (-R)..R,
        v15OdlyzkoEndpointIntegrand ((-1 : ℂ) + (y : ℂ) * I)) =
        -∫ t in (-R)..R,
          v15OdlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ ↦ v15OdlyzkoEndpointIntegrand
        ((2 : ℂ) + (t : ℂ) * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  norm_num
  rw [hfold]
  ring

private lemma v15OdlyzkoEndpoint_inv_two_pi_I_mul_I (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) =
      (1 / (2 * Real.pi) : ℂ) * X := by
  have hPi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [I_ne_zero, hPi]

/-- The finite endpoint rectangle splits into its horizontal error and twice
the truncated right-line integral. -/
theorem v15OdlyzkoEndpoint_rectangle_decomposition (R : ℝ) :
    RectangleIntegral' v15OdlyzkoEndpointIntegrand
        (v15OdlyzkoContourLower 2 R) (v15OdlyzkoContourUpper 2 R) =
      (1 / (2 * Real.pi * I) : ℂ) *
        (HIntegral v15OdlyzkoEndpointIntegrand (-1) 2 (-R) -
          HIntegral v15OdlyzkoEndpointIntegrand (-1) 2 R) +
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-R)..R,
          2 * v15OdlyzkoEndpointIntegrand
            ((2 : ℂ) + (t : ℂ) * I) := by
  have e₁ : (v15OdlyzkoContourLower 2 R).re = -1 := by
    norm_num [v15OdlyzkoContourLower]
  have e₂ : (v15OdlyzkoContourLower 2 R).im = -R := by
    simp [v15OdlyzkoContourLower]
  have e₃ : (v15OdlyzkoContourUpper 2 R).re = 2 := by
    simp [v15OdlyzkoContourUpper]
  have e₄ : (v15OdlyzkoContourUpper 2 R).im = R := by
    simp [v15OdlyzkoContourUpper]
  rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e₁, e₂, e₃, e₄]
  rw [show ∀ A B V₁ V₂ : ℂ,
      A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from
        fun _ _ _ _ ↦ by ring,
    v15OdlyzkoEndpointIntegrand_verticals_eq R, smul_eq_mul, mul_add,
    v15OdlyzkoEndpoint_inv_two_pi_I_mul_I]

/-- Both horizontal endpoint integrals vanish along the elementary height
sequence `R_n = n + 1`. -/
theorem v15OdlyzkoEndpoint_horizontal_vanish :
    Tendsto (fun n : ℕ ↦ HIntegral v15OdlyzkoEndpointIntegrand
      (-1) 2 (-((n : ℝ) + 1))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ HIntegral v15OdlyzkoEndpointIntegrand
      (-1) 2 ((n : ℝ) + 1)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hPhi⟩ := v15OdlyzkoPhi_exists_wideFourthPowerBound
  have hbound : ∀ (n : ℕ) (y : ℝ),
      (y = (n : ℝ) + 1 ∨ y = -((n : ℝ) + 1)) →
      ‖HIntegral v15OdlyzkoEndpointIntegrand (-1) 2 y‖ ≤
        6 * D / ((n : ℝ) + 1) := by
    intro n y hy
    let R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    have hyAbs : |y| = R := by
      rcases hy with rfl | rfl
      · exact abs_of_pos hR
      · rw [abs_neg, abs_of_pos hR]
    unfold HIntegral
    have hIntegral :
        ‖∫ x in (-1 : ℝ)..2,
          v15OdlyzkoEndpointIntegrand ((x : ℂ) + (y : ℂ) * I)‖ ≤
          (2 * D / R) * |(2 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      let s : ℂ := (x : ℂ) + (y : ℂ) * I
      have hsre : s.re = x := by simp [s]
      have hsim : s.im = y := by simp [s]
      have hsimAbs : |s.im| = R := by rw [hsim, hyAbs]
      have hyne : y ≠ 0 := by
        intro h
        rw [h, abs_zero] at hyAbs
        linarith
      have hs0 : s ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        rw [hsim] at him
        norm_num at him
        exact hyne him
      have hs1 : s ≠ 1 := by
        intro h
        have him := congrArg Complex.im h
        rw [hsim] at him
        norm_num at him
        exact hyne him
      have hPhiRaw := hPhi s
        (by rw [hsre]; linarith [hx.1])
        (by rw [hsre]; linarith [hx.2])
      have hDen : 1 ≤ (1 + |s.im|) ^ 4 := by
        nlinarith [abs_nonneg s.im,
          sq_nonneg (1 + |s.im|), sq_nonneg ((1 + |s.im|) ^ 2 - 1)]
      have hPhiD : ‖v15OdlyzkoPhi s‖ ≤ D := by
        apply hPhiRaw.trans
        rw [div_le_iff₀ (by positivity : 0 < (1 + |s.im|) ^ 4)]
        nlinarith
      have hnorm0 : R ≤ ‖s‖ := by
        rw [← hsimAbs]
        exact Complex.abs_im_le_norm s
      have hnorm1 : R ≤ ‖s - 1‖ := by
        have himSub : (s - 1).im = s.im := by simp
        rw [← hsimAbs, ← himSub]
        exact Complex.abs_im_le_norm (s - 1)
      have hinv0 : ‖1 / s‖ ≤ 1 / R := by
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hR hnorm0
      have hinv1 : ‖1 / (s - 1)‖ ≤ 1 / R := by
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hR hnorm1
      rw [v15OdlyzkoEndpointIntegrand,
        v15OdlyzkoEndpointPolynomial_logDeriv hs0 hs1, norm_mul]
      have hfrac : ‖1 / s + 1 / (s - 1)‖ ≤ 2 / R := by
        calc
          ‖1 / s + 1 / (s - 1)‖ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ :=
            norm_add_le _ _
          _ ≤ 1 / R + 1 / R := add_le_add hinv0 hinv1
          _ = 2 / R := by ring
      calc
        ‖v15OdlyzkoPhi s‖ * ‖1 / s + 1 / (s - 1)‖ ≤ D * (2 / R) :=
          mul_le_mul hPhiD hfrac (norm_nonneg _) hD
        _ = 2 * D / R := by ring
    calc
      ‖∫ x in (-1 : ℝ)..2,
          v15OdlyzkoEndpointIntegrand ((x : ℂ) + (y : ℂ) * I)‖ ≤
          (2 * D / R) * |(2 : ℝ) - (-1)| := hIntegral
      _ = 6 * D / ((n : ℝ) + 1) := by
        rw [show |(2 : ℝ) - (-1)| = 3 by norm_num]
        dsimp only [R]
        ring
  have hMajorant : Tendsto (fun n : ℕ ↦ 6 * D / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  exact ⟨
    squeeze_zero_norm (fun n ↦ hbound n (-((n : ℝ) + 1)) (Or.inr rfl)) hMajorant,
    squeeze_zero_norm (fun n ↦ hbound n ((n : ℝ) + 1) (Or.inl rfl)) hMajorant⟩

/-- The twice-right endpoint integrand is absolutely integrable. -/
theorem v15OdlyzkoEndpoint_twice_right_integrable :
    Integrable (fun t : ℝ ↦ 2 * v15OdlyzkoEndpointIntegrand
      ((2 : ℂ) + (t : ℂ) * I)) volume := by
  exact v15OdlyzkoEndpointIntegrand_right_vertical_integrable.const_mul 2

/-- Symmetric truncations of the twice-right endpoint integral converge to
the full-line integral along the elementary height sequence. -/
theorem v15OdlyzkoEndpoint_twice_right_tendsto :
    Tendsto (fun n : ℕ ↦ ∫ t in (-((n : ℝ) + 1))..((n : ℝ) + 1),
      2 * v15OdlyzkoEndpointIntegrand ((2 : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, 2 * v15OdlyzkoEndpointIntegrand
        ((2 : ℂ) + (t : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    v15OdlyzkoEndpoint_twice_right_integrable
    (tendsto_neg_atTop_atBot.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- The normalized endpoint rectangles converge to the normalized twice-right
full-line integral. -/
theorem v15OdlyzkoEndpoint_rectangle_tendsto :
    Tendsto (fun n : ℕ ↦
      RectangleIntegral' v15OdlyzkoEndpointIntegrand
        (v15OdlyzkoContourLower 2 ((n : ℝ) + 1))
        (v15OdlyzkoContourUpper 2 ((n : ℝ) + 1))) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, 2 * v15OdlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I))) := by
  rcases v15OdlyzkoEndpoint_horizontal_vanish with ⟨hBottom, hTop⟩
  have hHorizontal :=
    ((hBottom.sub hTop).const_mul (1 / (2 * Real.pi * I) : ℂ))
  have hVertical :=
    v15OdlyzkoEndpoint_twice_right_tendsto.const_mul
      (1 / (2 * Real.pi) : ℂ)
  have hLimit := hHorizontal.add hVertical
  simp only [sub_zero, mul_zero, zero_add] at hLimit
  exact hLimit.congr fun n ↦
    (v15OdlyzkoEndpoint_rectangle_decomposition ((n : ℝ) + 1)).symm

/-- The two pole-removal endpoints contribute exactly `32/3` to the
normalized full-line formula. -/
theorem v15OdlyzkoEndpoint_normalized_integral :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, 2 * v15OdlyzkoEndpointIntegrand
          ((2 : ℂ) + (t : ℂ) * I) =
      32 / 3 := by
  have hConstant :
      Tendsto (fun n : ℕ ↦
        RectangleIntegral' v15OdlyzkoEndpointIntegrand
          (v15OdlyzkoContourLower 2 ((n : ℝ) + 1))
          (v15OdlyzkoContourUpper 2 ((n : ℝ) + 1))) atTop
        (𝓝 (v15OdlyzkoPhi 0 + v15OdlyzkoPhi 1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    exact (v15OdlyzkoEndpoint_rectangleIntegral (by positivity)).symm
  have hUnique := tendsto_nhds_unique
    v15OdlyzkoEndpoint_rectangle_tendsto hConstant
  rw [v15OdlyzkoPhi_zero_add_one] at hUnique
  exact hUnique

end

end TraceEuclidean
