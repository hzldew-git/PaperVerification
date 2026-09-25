import TraceEuclidean.V15OdlyzkoContourSequence
import TraceEuclidean.V15OdlyzkoPrimeTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical limits in the Odlyzko contour argument

The Landau partial-fraction estimate gives a quadratic bound for the
logarithmic derivative of the completed Dedekind zeta on `Re(s) = 2`.
Together with the fourth-power decay of the exact Odlyzko transform, this
proves absolute integrability of the right vertical side and convergence of
its symmetric truncations.
-/

namespace TraceEuclidean

noncomputable section

open Complex Set Filter Topology MeasureTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The line `Re(s) = 2` lies in the inner disk used by the polynomial
Landau estimate, with the disk parameter chosen to be the line height. -/
lemma v15_right_vertical_mem_landau_inner_ball (c : ℂ) (t : ℝ) :
    (2 : ℂ) + (t : ℂ) * I ∈ Metric.closedBall c
      (83 / 100 * v15DedekindZetaLandauRadius c t) := by
  have hcre : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
  have hcim : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖(2 : ℂ) + (t : ℂ) * I - c‖ ≤
        |((2 : ℂ) + (t : ℂ) * I - c).re| +
          |((2 : ℂ) + (t : ℂ) * I - c).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |2 - c.re| + |t - c.im| := by simp
    _ ≤ (2 + |c.re|) + (|t| + |c.im|) := by
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      simpa [htwo] using add_le_add (abs_sub (2 : ℝ) c.re) (abs_sub t c.im)
    _ ≤ 2 + ‖c‖ + (|t| + ‖c‖) := by linarith
    _ ≤ 83 / 100 * v15DedekindZetaLandauRadius c t := by
      dsimp [v15DedekindZetaLandauRadius]
      nlinarith [norm_nonneg c, abs_nonneg t]

/-- On the absolute-convergence line `Re(s) = 2`, the logarithmic
derivative of the pole-removed completed zeta has at most quadratic growth.
The proof uses only the global Landau data and the proved location of every
zero in the closed critical strip. -/
theorem exists_v15_completedZetaPoleRemoved_right_vertical_quadratic_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ t : ℝ,
      ‖logDeriv
        (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
        ((2 : ℂ) + (t : ℂ) * I)‖ ≤ Cv * (1 + |t|) ^ 2 := by
  classical
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  obtain ⟨c, C, hC, hLandau⟩ :=
    exists_v15_completedZetaPoleRemoved_polynomial_landau_data K
  refine ⟨2 * C, by positivity, ?_⟩
  intro t
  obtain ⟨Z, hZ, hCount, hError⟩ := hLandau t
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hsInner : s ∈ Metric.closedBall c
      (83 / 100 * v15DedekindZetaLandauRadius c t) := by
    simpa only [s] using v15_right_vertical_mem_landau_inner_ball c t
  have hsRe : s.re = 2 := by simp [s]
  have hsNonzero : F s ≠ 0 := by
    apply v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
    rw [hsRe]
    norm_num
  have hRegular := hError s hsInner hsNonzero
  have hTerm : ∀ ρ ∈ Z,
      ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        (analyticOrderNatAt F ρ : ℝ) := by
    intro ρ hρ
    have hρSet : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at hρSet
    have hstrip := v15_completedZetaPoleRemoved_zero_mem_closedStrip
      (K := K) hρSet.2
    have hre : 1 ≤ |(s - ρ).re| := by
      rw [Complex.sub_re, hsRe, abs_of_nonneg]
      · linarith [hstrip.2]
      · linarith [hstrip.2]
    have hdist : 1 ≤ ‖s - ρ‖ :=
      hre.trans (Complex.abs_re_le_norm (s - ρ))
    have hdistPos : 0 < ‖s - ρ‖ := lt_of_lt_of_le zero_lt_one hdist
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hdistPos).2
    have hOrder : 0 ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hZeroSum :
      ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ ≤
        C * (1 + |t|) ^ 2 := by
    calc
      _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) := by
        exact Finset.sum_le_sum fun ρ hρ ↦ hTerm ρ hρ
      _ ≤ C * (1 + |t|) ^ 2 := hCount
  calc
    ‖logDeriv F s‖ ≤
        ‖logDeriv F s -
          ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℂ) / (s - ρ)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ C * (1 + |t|) ^ 2 + C * (1 + |t|) ^ 2 :=
      add_le_add hRegular hZeroSum
    _ = (2 * C) * (1 + |t|) ^ 2 := by ring

/-- The completed logarithmic derivative is continuous along the zero-free
line `Re(s) = 2`. -/
theorem v15_completedZetaPoleRemoved_logDeriv_right_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun t : ℝ ↦
      logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
        ((2 : ℂ) + (t : ℂ) * I)) := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  let g : ℝ → ℂ := fun u ↦ (2 : ℂ) + (u : ℂ) * I
  change Continuous ((fun z : ℂ ↦ deriv F z / F z) ∘ g)
  have hLine : Continuous g := by
    dsimp only [g]
    fun_prop
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  have hAnalytic : AnalyticAt ℂ F (g t) :=
    DedekindZeta.GlobalContinuation.completedZetaPoleRemoved_analyticOn K
      (g t) (mem_univ (g t))
  have hFne : F (g t) ≠ 0 := by
    apply v15_completedZetaPoleRemoved_ne_zero_of_one_lt_re
    simp [g]
  have hQuot : ContinuousAt (fun z : ℂ ↦ deriv F z / F z) (g t) :=
    hAnalytic.deriv.continuousAt.div hAnalytic.continuousAt hFne
  exact hQuot.comp hLine.continuousAt

/-- The completed-zeta integrand is absolutely integrable on the right
vertical line. -/
theorem v15OdlyzkoCompletedIntegrand_right_vertical_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (fun t : ℝ ↦
      v15OdlyzkoCompletedIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)) volume := by
  obtain ⟨D, hD, hPhi⟩ :=
    v15OdlyzkoPhi_vertical_exists_fourthPowerBound 2
  obtain ⟨Cv, hCv, hLog⟩ :=
    exists_v15_completedZetaPoleRemoved_right_vertical_quadratic_bound K
  apply (v15OdlyzkoCriticalMajorant_two_integrable (D * Cv)).mono'
  · exact ((v15OdlyzkoPhi_differentiable.continuous.comp
      (by fun_prop : Continuous
        (fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I))).mul
      (v15_completedZetaPoleRemoved_logDeriv_right_continuous K)).aestronglyMeasurable
  · filter_upwards with t
    let u : ℝ := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have hPhi' :
        ‖v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I)‖ ≤ D / u ^ 4 := by
      convert hPhi t using 1 <;> norm_num [u]
    have hLog' :
        ‖logDeriv
          (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
          ((2 : ℂ) + (t : ℂ) * I)‖ ≤ Cv * u ^ 2 := by
      simpa only [u] using hLog t
    rw [norm_mul]
    calc
      _ ≤ (D / u ^ 4) * (Cv * u ^ 2) :=
        mul_le_mul hPhi' hLog' (norm_nonneg _) (by positivity)
      _ = D * Cv / u ^ 2 := by field_simp

/-- Symmetric truncations of the right vertical integral converge to the
full-line integral along any sequence of heights tending to infinity. -/
theorem v15OdlyzkoCompletedIntegrand_right_vertical_tendsto
    (K : Type*) [Field K] [NumberField K]
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ ↦ ∫ t in (-(R n))..R n,
      v15OdlyzkoCompletedIntegrand K
        ((2 : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, v15OdlyzkoCompletedIntegrand K
        ((2 : ℂ) + (t : ℂ) * I))) := by
  exact intervalIntegral_tendsto_integral
    (v15OdlyzkoCompletedIntegrand_right_vertical_integrable K)
    (tendsto_neg_atTop_atBot.comp hR) hR

/-- The folded full-line integrand obtained by combining the two vertical
sides of the symmetric rectangle. -/
def v15OdlyzkoCompletedVerticalPair
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℂ :=
  (v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) +
      v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I)) *
    logDeriv (DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K)
      ((2 : ℂ) + (t : ℂ) * I)

/-- Transform symmetry makes the folded vertical integrand twice the right
vertical integrand. -/
theorem v15OdlyzkoCompletedVerticalPair_eq_two_mul
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    v15OdlyzkoCompletedVerticalPair K t =
      2 * v15OdlyzkoCompletedIntegrand K
        ((2 : ℂ) + (t : ℂ) * I) := by
  have hreflect :
      ((-1 : ℂ) - (t : ℂ) * I) =
        1 - ((2 : ℂ) + (t : ℂ) * I) := by ring
  rw [v15OdlyzkoCompletedVerticalPair, hreflect,
    v15OdlyzkoPhi_one_sub]
  ring

/-- The folded vertical integrand is absolutely integrable. -/
theorem v15OdlyzkoCompletedVerticalPair_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable (v15OdlyzkoCompletedVerticalPair K) volume := by
  have h :=
    (v15OdlyzkoCompletedIntegrand_right_vertical_integrable K).const_mul
      (2 : ℂ)
  apply h.congr
  filter_upwards with t
  exact (v15OdlyzkoCompletedVerticalPair_eq_two_mul K t).symm

/-- Folding the left vertical side onto the right one. -/
theorem v15OdlyzkoCompletedIntegrand_verticals_eq
    (K : Type*) [Field K] [NumberField K] (R : ℝ) :
    VIntegral (v15OdlyzkoCompletedIntegrand K) 2 (-R) R -
        VIntegral (v15OdlyzkoCompletedIntegrand K) (-1) (-R) R =
      I • ∫ t in (-R)..R, v15OdlyzkoCompletedVerticalPair K t := by
  let F := DedekindZeta.GlobalContinuation.completedZetaPoleRemoved K
  let L := logDeriv F
  have hLc : Continuous
      (fun t : ℝ ↦ L ((2 : ℂ) + (t : ℂ) * I)) := by
    simpa only [L, F] using
      v15_completedZetaPoleRemoved_logDeriv_right_continuous K
  have hPhiRight : Continuous
      (fun t : ℝ ↦ v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I)) :=
    v15OdlyzkoPhi_differentiable.continuous.comp (by fun_prop)
  have hPhiReflect : Continuous
      (fun t : ℝ ↦ v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I)) :=
    v15OdlyzkoPhi_differentiable.continuous.comp (by fun_prop)
  have hleft : ∀ y : ℝ,
      v15OdlyzkoPhi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I) =
        -(v15OdlyzkoPhi ((-1 : ℂ) - ((-y : ℝ) : ℂ) * I) *
          L ((2 : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs :
        ((-1 : ℂ) + (y : ℂ) * I) =
          1 - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast
      ring
    change
      v15OdlyzkoPhi ((-1 : ℂ) + (y : ℂ) * I) *
          logDeriv F ((-1 : ℂ) + (y : ℂ) * I) =
        -(v15OdlyzkoPhi ((-1 : ℂ) - ((-y : ℝ) : ℂ) * I) *
          logDeriv F ((2 : ℂ) + ((-y : ℝ) : ℂ) * I))
    rw [hs, DedekindZeta.LogDeriv.logDeriv_completedZetaPoleRemoved_one_sub]
    have hreflect :
        (1 : ℂ) - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) =
          (-1 : ℂ) - ((-y : ℝ) : ℂ) * I := by ring
    rw [hreflect]
    ring
  have hI1 : IntervalIntegrable
      (fun t : ℝ ↦ v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I)) volume (-R) R :=
    (hPhiRight.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun t : ℝ ↦ v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I)) volume (-R) R :=
    (hPhiReflect.mul hLc).intervalIntegrable _ _
  have hfold :
      (∫ y in (-R)..R,
        v15OdlyzkoPhi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I)) =
        -∫ t in (-R)..R,
          v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I) *
            L ((2 : ℂ) + (t : ℂ) * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ ↦ v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I) *
        L ((2 : ℂ) + (t : ℂ) * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral, v15OdlyzkoCompletedIntegrand]
  norm_num
  change
    (I • ∫ y in (-R)..R,
      v15OdlyzkoPhi ((2 : ℂ) + (y : ℂ) * I) *
        L ((2 : ℂ) + (y : ℂ) * I)) -
      (I • ∫ y in (-R)..R,
        v15OdlyzkoPhi ((-1 : ℂ) + (y : ℂ) * I) *
          L ((-1 : ℂ) + (y : ℂ) * I)) =
        I • ∫ t in (-R)..R, v15OdlyzkoCompletedVerticalPair K t
  rw [hfold, ← smul_sub, sub_neg_eq_add,
    ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  change
    v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) *
          L ((2 : ℂ) + (t : ℂ) * I) +
        v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I) *
          L ((2 : ℂ) + (t : ℂ) * I) =
      (v15OdlyzkoPhi ((2 : ℂ) + (t : ℂ) * I) +
          v15OdlyzkoPhi ((-1 : ℂ) - (t : ℂ) * I)) *
        L ((2 : ℂ) + (t : ℂ) * I)
  ring

/-- Symmetric truncations of the folded vertical integrand converge to its
full-line integral. -/
theorem v15OdlyzkoCompletedVerticalPair_tendsto
    (K : Type*) [Field K] [NumberField K]
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ ↦ ∫ t in (-(R n))..R n,
      v15OdlyzkoCompletedVerticalPair K t) atTop
      (𝓝 (∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t)) := by
  exact intervalIntegral_tendsto_integral
    (v15OdlyzkoCompletedVerticalPair_integrable K)
    (tendsto_neg_atTop_atBot.comp hR) hR

/-- The elementary scalar identity converting the normalized vertical
contour factor into the real `1 / (2π)` normalization. -/
lemma v15_inv_two_pi_I_mul_I (X : ℂ) :
    (1 / (2 * Real.pi * I) : ℂ) * (I * X) =
      (1 / (2 * Real.pi) : ℂ) * X := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hPi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp

/-- The four pieces of each finite rectangle split into a horizontal error
and the truncated folded vertical integral. -/
theorem v15OdlyzkoContourSequence_rectangle_decomposition
    (K : Type*) [Field K] [NumberField K]
    (data : V15OdlyzkoContourSequenceData K) (n : ℕ) :
    RectangleIntegral' (v15OdlyzkoCompletedIntegrand K)
        (v15OdlyzkoContourLower 2 (data.R n))
        (v15OdlyzkoContourUpper 2 (data.R n)) =
      (1 / (2 * Real.pi * I) : ℂ) *
        (HIntegral (v15OdlyzkoCompletedIntegrand K) (-1) 2 (-(data.R n)) -
          HIntegral (v15OdlyzkoCompletedIntegrand K) (-1) 2 (data.R n)) +
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-(data.R n))..data.R n,
          v15OdlyzkoCompletedVerticalPair K t := by
  have e₁ : (v15OdlyzkoContourLower 2 (data.R n)).re = -1 := by
    norm_num [v15OdlyzkoContourLower]
  have e₂ : (v15OdlyzkoContourLower 2 (data.R n)).im = -(data.R n) := by
    simp [v15OdlyzkoContourLower]
  have e₃ : (v15OdlyzkoContourUpper 2 (data.R n)).re = 2 := by
    simp [v15OdlyzkoContourUpper]
  have e₄ : (v15OdlyzkoContourUpper 2 (data.R n)).im = data.R n := by
    simp [v15OdlyzkoContourUpper]
  rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e₁, e₂, e₃, e₄]
  have hVertical :=
    v15OdlyzkoCompletedIntegrand_verticals_eq K (data.R n)
  rw [show ∀ A B V₁ V₂ : ℂ,
      A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from
        fun _ _ _ _ ↦ by ring,
    hVertical, smul_eq_mul, mul_add, v15_inv_two_pi_I_mul_I]

/-- Along the good-height sequence, the normalized finite rectangle
integrals converge to the folded full-line integral. -/
theorem v15OdlyzkoContourSequence_rectangle_tendsto
    (K : Type*) [Field K] [NumberField K]
    (data : V15OdlyzkoContourSequenceData K) :
    Tendsto (fun n : ℕ ↦
      RectangleIntegral' (v15OdlyzkoCompletedIntegrand K)
        (v15OdlyzkoContourLower 2 (data.R n))
        (v15OdlyzkoContourUpper 2 (data.R n))) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t)) := by
  have hHorizontal :=
    ((data.horizontal_bottom_vanish.sub data.horizontal_top_vanish).const_mul
      (1 / (2 * Real.pi * I) : ℂ))
  have hVertical :=
    (v15OdlyzkoCompletedVerticalPair_tendsto K data.R_tendsto).const_mul
      (1 / (2 * Real.pi) : ℂ)
  have hLimit := hHorizontal.add hVertical
  simp only [sub_zero, mul_zero, zero_add] at hLimit
  exact hLimit.congr fun n ↦
    (v15OdlyzkoContourSequence_rectangle_decomposition K data n).symm

/-- The limiting vertical expression has nonnegative real part.  This is
the explicit-formula inequality obtained directly from finite zero sums, so
it does not require an ordered enumeration of all completed-zeta zeros. -/
theorem v15OdlyzkoCompletedVerticalPair_integral_re_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t).re := by
  classical
  let data : V15OdlyzkoContourSequenceData K :=
    Classical.choice (exists_v15_odlyzkoContourSequenceData K)
  have hLimit := v15OdlyzkoContourSequence_rectangle_tendsto K data
  have hLimitRe :
      Tendsto (fun n : ℕ ↦
        (RectangleIntegral' (v15OdlyzkoCompletedIntegrand K)
          (v15OdlyzkoContourLower 2 (data.R n))
          (v15OdlyzkoContourUpper 2 (data.R n))).re) atTop
        (𝓝 (((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, v15OdlyzkoCompletedVerticalPair K t).re)) :=
    (Complex.continuous_re.tendsto _).comp hLimit
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hLimitRe
  filter_upwards with n
  rw [data.rectangle_identity n]
  exact data.zero_sum_re_nonneg n

end

end TraceEuclidean
