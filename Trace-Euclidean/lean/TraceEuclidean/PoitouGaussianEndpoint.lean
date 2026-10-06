import TraceEuclidean.PoitouGaussianLimit

/-!
# Endpoint terms for the Gaussian-regularized Poitou kernel

The two pole-removal residues at `s = 0, 1` add up to four times the
positive-half-line integral of the regularized test function.  Combined with
`PoitouGaussianLimit`, this gives Poitou's exact endpoint correction after
the Gaussian is removed.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open Filter MeasureTheory Complex Set
open scoped Topology ComplexConjugate

theorem poitouGaussian_even (ε x : ℝ) :
    poitouGaussian ε (-x) = poitouGaussian ε x := by
  simp [poitouGaussian]

theorem poitouGaussianRegularizedKernel_even (y ε x : ℝ) :
    poitouGaussianRegularizedKernel y ε (-x) =
      poitouGaussianRegularizedKernel y ε x := by
  rw [poitouGaussianRegularizedKernel, poitouGaussianRegularizedKernel,
    poitouFullKernel_even, poitouGaussian_even]

theorem poitouGaussianRegularizedKernel_mul_exp_integrable
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ ↦
      poitouGaussianRegularizedKernel y ε x * Real.exp (t * x)) volume := by
  have hbase := (poitouGaussian_mul_exp_integrable hε t).const_mul (9 / 4 : ℝ)
  apply hbase.mono'
  · exact ((poitouGaussianRegularizedKernel_continuous y ε).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (poitouGaussianRegularizedKernel_nonneg y ε x) (Real.exp_pos _).le)]
    calc
      poitouGaussianRegularizedKernel y ε x * Real.exp (t * x) =
          poitouFullKernel y x *
            (poitouGaussian ε x * Real.exp (t * x)) := by
        unfold poitouGaussianRegularizedKernel
        ring
      _ ≤ (9 / 4 : ℝ) *
          (poitouGaussian ε x * Real.exp (t * x)) :=
        mul_le_mul_of_nonneg_right (poitouFullKernel_le_nine_fourths y x)
          (mul_nonneg (poitouGaussian_nonneg ε x) (Real.exp_pos _).le)

theorem poitouGaussianRegularizedPhi_one_sub (y ε : ℝ) (s : ℂ) :
    poitouGaussianRegularizedPhi y ε (1 - s) =
      poitouGaussianRegularizedPhi y ε s := by
  unfold poitouGaussianRegularizedPhi
  calc
    (∫ x : ℝ, (poitouGaussianRegularizedKernel y ε x : ℂ) *
        Complex.exp (((1 - s) - (1 / 2 : ℂ)) * (x : ℂ))) =
      ∫ x : ℝ, (poitouGaussianRegularizedKernel y ε (-x) : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [poitouGaussianRegularizedKernel_even]
      congr 1
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, (poitouGaussianRegularizedKernel y ε x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
      exact integral_neg_eq_self
        (fun x : ℝ ↦ (poitouGaussianRegularizedKernel y ε x : ℂ) *
          Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) volume

theorem poitouGaussianRegularizedPhi_conj (y ε : ℝ) (s : ℂ) :
    poitouGaussianRegularizedPhi y ε (conj s) =
      conj (poitouGaussianRegularizedPhi y ε s) := by
  unfold poitouGaussianRegularizedPhi
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_sub, map_div₀, map_ofNat]
  simp

/-- Positivity extends from the open strip to its boundary by continuity.
The Gaussian regularization is essential here: its transform is entire. -/
theorem poitouGaussianRegularizedPhi_re_nonneg_of_mem_closed_strip
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (s : ℂ)
    (hs₁ : 0 ≤ s.re) (hs₂ : s.re ≤ 1) :
    0 ≤ (poitouGaussianRegularizedPhi y ε s).re := by
  rcases hs₁.eq_or_lt with hsZero | hsPos
  · have hsre : s.re = 0 := hsZero.symm
    have heps : Tendsto (fun n : ℕ ↦ poitouGaussianEpsilon (n + 1))
        atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 poitouGaussianEpsilon_tendsto_zero
    have hsT : Tendsto
        (fun n : ℕ ↦ s + (poitouGaussianEpsilon (n + 1) : ℂ))
        atTop (𝓝 s) := by
      convert tendsto_const_nhds.add heps.ofReal using 1 <;> simp
    have hphi :=
      (poitouGaussianRegularizedPhi_differentiable (y := y) hε).continuous.continuousAt.tendsto.comp hsT
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hphi
    apply ge_of_tendsto hre
    filter_upwards with n
    apply poitouGaussianRegularizedPhi_re_nonneg_of_mem_open_strip hy hε
    · simp [hsre, poitouGaussianEpsilon_pos]
    · change (s + (poitouGaussianEpsilon (n + 1) : ℂ)).re < 1
      simp only [add_re, ofReal_re]
      rw [hsre]
      simp only [zero_add]
      unfold poitouGaussianEpsilon
      rw [div_lt_one (by positivity : (0 : ℝ) < (n + 1 : ℕ) + 1)]
      norm_num
      positivity
  · rcases hs₂.eq_or_lt with hsOne | hsLt
    · have hsre : s.re = 1 := hsOne
      have heps : Tendsto (fun n : ℕ ↦ poitouGaussianEpsilon (n + 1))
          atTop (𝓝 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2 poitouGaussianEpsilon_tendsto_zero
      have hsT : Tendsto
          (fun n : ℕ ↦ s - (poitouGaussianEpsilon (n + 1) : ℂ))
          atTop (𝓝 s) := by
        convert tendsto_const_nhds.sub heps.ofReal using 1 <;> simp
      have hphi :=
        (poitouGaussianRegularizedPhi_differentiable (y := y) hε).continuous.continuousAt.tendsto.comp hsT
      have hre := Complex.continuous_re.continuousAt.tendsto.comp hphi
      apply ge_of_tendsto hre
      filter_upwards with n
      apply poitouGaussianRegularizedPhi_re_nonneg_of_mem_open_strip hy hε
      · change 0 < (s - (poitouGaussianEpsilon (n + 1) : ℂ)).re
        simp only [sub_re, ofReal_re]
        rw [hsre]
        unfold poitouGaussianEpsilon
        rw [sub_pos, div_lt_one (by positivity : (0 : ℝ) < (n + 1 : ℕ) + 1)]
        norm_num
        positivity
      · simp [hsre, poitouGaussianEpsilon_pos]
    · exact poitouGaussianRegularizedPhi_re_nonneg_of_mem_open_strip
        hy hε s hsPos hsLt

private def poitouGaussianPositiveEndpoint (y ε x : ℝ) : ℝ :=
  poitouGaussianRegularizedKernel y ε x * Real.exp (x / 2)

private def poitouGaussianNegativeEndpoint (y ε x : ℝ) : ℝ :=
  poitouGaussianRegularizedKernel y ε x * Real.exp (-x / 2)

private theorem poitouGaussianPositiveEndpoint_integrable
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (poitouGaussianPositiveEndpoint y ε) volume := by
  convert poitouGaussianRegularizedKernel_mul_exp_integrable y hε (1 / 2) using 1
  funext x
  simp only [poitouGaussianPositiveEndpoint]
  congr 2
  ring

private theorem poitouGaussianNegativeEndpoint_integrable
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (poitouGaussianNegativeEndpoint y ε) volume := by
  convert poitouGaussianRegularizedKernel_mul_exp_integrable y hε (-(1 / 2)) using 1
  funext x
  simp only [poitouGaussianNegativeEndpoint]
  congr 2
  ring

private theorem poitouGaussianRegularizedPhi_one_eq_endpoint
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poitouGaussianRegularizedPhi y ε 1 =
      ((∫ x : ℝ, poitouGaussianPositiveEndpoint y ε x : ℝ) : ℂ) := by
  unfold poitouGaussianRegularizedPhi
  calc
    (∫ x : ℝ, (poitouGaussianRegularizedKernel y ε x : ℂ) *
      Complex.exp (((1 : ℂ) - 1 / 2) * (x : ℂ))) =
        ∫ x : ℝ, (poitouGaussianPositiveEndpoint y ε x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((1 : ℂ) - 1 / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (x / 2)).symm]
      simp [poitouGaussianPositiveEndpoint]
    _ = _ := integral_ofReal

private theorem poitouGaussianRegularizedPhi_zero_eq_endpoint
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poitouGaussianRegularizedPhi y ε 0 =
      ((∫ x : ℝ, poitouGaussianNegativeEndpoint y ε x : ℝ) : ℂ) := by
  unfold poitouGaussianRegularizedPhi
  calc
    (∫ x : ℝ, (poitouGaussianRegularizedKernel y ε x : ℂ) *
      Complex.exp (((0 : ℂ) - 1 / 2) * (x : ℂ))) =
        ∫ x : ℝ, (poitouGaussianNegativeEndpoint y ε x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((0 : ℂ) - 1 / 2) * (x : ℂ) = ((-x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (-x / 2)).symm]
      simp [poitouGaussianNegativeEndpoint]
    _ = _ := integral_ofReal

private theorem poitouGaussian_endpoint_pointwise (y ε x : ℝ) :
    poitouGaussianPositiveEndpoint y ε x +
        poitouGaussianNegativeEndpoint y ε x =
      2 * (poitouScaledTest y x * poitouGaussian ε x) := by
  unfold poitouGaussianPositiveEndpoint poitouGaussianNegativeEndpoint
    poitouGaussianRegularizedKernel poitouFullKernel
  rw [Real.cosh_eq]
  have hden : Real.exp (x / 2) + Real.exp (-(x / 2)) ≠ 0 := by positivity
  field_simp [hden]

private theorem poitouGaussianScaledTest_integral_univ_eq_Ioi
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) :
    (∫ x : ℝ, poitouScaledTest y x * poitouGaussian ε x) =
      2 * ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouGaussian ε x := by
  let f : ℝ → ℝ := fun x ↦ poitouScaledTest y x * poitouGaussian ε x
  have heven (x : ℝ) : f |x| = f x := by
    dsimp only [f]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, poitouScaledTest_even, poitouGaussian_even]
  calc
    (∫ x : ℝ, poitouScaledTest y x * poitouGaussian ε x) =
        ∫ x : ℝ, f |x| := by
      apply integral_congr_ae
      filter_upwards with x
      exact (heven x).symm
    _ = 2 * ∫ x in Ioi (0 : ℝ), f x := integral_comp_abs
    _ = _ := rfl

/-- Exact endpoint identity for every positive regularization parameter. -/
theorem poitouGaussianRegularizedPhi_zero_add_one
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) :
    poitouGaussianRegularizedPhi y ε 0 +
        poitouGaussianRegularizedPhi y ε 1 =
      ((4 * ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouGaussian ε x : ℝ) : ℂ) := by
  rw [poitouGaussianRegularizedPhi_zero_eq_endpoint y hε,
    poitouGaussianRegularizedPhi_one_eq_endpoint y hε]
  rw [← ofReal_add]
  rw [add_comm (∫ x : ℝ, poitouGaussianNegativeEndpoint y ε x), ← integral_add
    (poitouGaussianPositiveEndpoint_integrable y hε)
    (poitouGaussianNegativeEndpoint_integrable y hε)]
  have hpoint : (fun x : ℝ ↦
      poitouGaussianPositiveEndpoint y ε x +
        poitouGaussianNegativeEndpoint y ε x) =
      fun x : ℝ ↦ 2 * (poitouScaledTest y x * poitouGaussian ε x) := by
    funext x
    exact poitouGaussian_endpoint_pointwise y ε x
  rw [hpoint, integral_const_mul,
    poitouGaussianScaledTest_integral_univ_eq_Ioi hy hε]
  push_cast
  ring

/-- The sum of the two regularized endpoint transforms converges to the
source value `12π / (5√y)`. -/
theorem poitouGaussianRegularizedPhi_zero_add_one_tendsto
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ ↦
      poitouGaussianRegularizedPhi y (poitouGaussianEpsilon n) 0 +
        poitouGaussianRegularizedPhi y (poitouGaussianEpsilon n) 1)
      atTop (𝓝 ((12 * Real.pi / (5 * Real.sqrt y) : ℝ) : ℂ)) := by
  have h :=
    (poitouGaussianRegularizedScaledTest_integral_Ioi_tendsto hy).const_mul 4
  have hc := h.ofReal
  convert hc using 1
  · funext n
    rw [poitouGaussianRegularizedPhi_zero_add_one hy
      (poitouGaussianEpsilon_pos n)]
  · push_cast
    congr 1
    ring

end
end TraceEuclidean.PoitouKernel
