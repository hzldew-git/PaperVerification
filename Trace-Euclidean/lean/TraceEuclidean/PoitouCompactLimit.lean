import TraceEuclidean.CompactExplicitFormulaClosed
import TraceEuclidean.PoitouCompactRegularization
import TraceEuclidean.PoitouCorrectionSeries
import TraceEuclidean.PoitouDifferenceQuotient
import TraceEuclidean.OdlyzkoArchimedeanBridge

/-!
# Removing the compact cutoff from Poitou's kernel

The cutoff radius is `n+1`.  This file proves the endpoint and archimedean
limits needed to pass the unconditional compact-kernel inequality to Poitou's
unregularized degree-eleven formula.
-/

namespace TraceEuclidean

noncomputable section

open Complex Filter MeasureTheory Set Topology

/-- The auxiliary function printed by Odlyzko is at most one on its defining
interval. -/
theorem odlyzkoHCore_le_one {t : ℝ} (ht₀ : 0 ≤ t) (ht₂ : t ≤ 2) :
    odlyzkoHCore t ≤ 1 := by
  have hcos : 1 + Real.cos (Real.pi * t) / 2 ≤ (3 / 2 : ℝ) := by
    linarith [Real.cos_le_one (Real.pi * t)]
  have hfirst :
      (2 - t) * (1 + Real.cos (Real.pi * t) / 2) / 3 ≤
        (2 - t) / 2 := by
    have h := mul_le_mul_of_nonneg_left hcos (sub_nonneg.mpr ht₂)
    nlinarith
  have hsin : Real.sin (Real.pi * t) ≤ Real.pi * t :=
    Real.sin_le (mul_nonneg Real.pi_pos.le ht₀)
  have hsecond :
      Real.sin (Real.pi * t) / (2 * Real.pi) ≤ t / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_pos]
  unfold odlyzkoHCore
  linarith

theorem odlyzkoH_le_one (x : ℝ) : odlyzkoH x ≤ 1 := by
  rw [odlyzkoH]
  split_ifs with hx
  · exact odlyzkoHCore_le_one (abs_nonneg x) hx
  · norm_num

theorem odlyzkoF4_le_one (x : ℝ) : odlyzkoF4 x ≤ 1 := by
  unfold odlyzkoF4
  apply (div_le_iff₀ (Real.cosh_pos (x / 2))).2
  simpa using (odlyzkoH_le_one (x / 4)).trans (Real.one_le_cosh (x / 2))

namespace PoitouKernel

open TraceEuclidean.PoitouDegreeEleven

theorem poitouCompactCutoff_le_one (R x : ℝ) :
    poitouCompactCutoff R x ≤ 1 :=
  TraceEuclidean.odlyzkoF4_le_one (x / R)

@[simp] theorem poitouCompactCutoff_zero {R : ℝ} (hR : R ≠ 0) :
    poitouCompactCutoff R 0 = 1 := by
  simp [poitouCompactCutoff, hR, TraceEuclidean.odlyzkoF4_zero]

/-- At every fixed point the expanding compact cutoff tends to one. -/
theorem poitouCompactCutoff_tendsto_one (x : ℝ) :
    Tendsto (fun n : ℕ ↦ poitouCompactCutoff ((n : ℝ) + 1) x)
      atTop (𝓝 1) := by
  have harg : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hx : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert hx.mul hinv using 1 <;> simp [div_eq_mul_inv]
  have h := TraceEuclidean.odlyzkoF4_continuous.continuousAt.tendsto.comp harg
  simpa [poitouCompactCutoff, TraceEuclidean.odlyzkoF4_zero,
    Function.comp_def] using h

/-- The compact kernel remains normalized at the origin. -/
theorem poitouCompactExplicitFormulaKernel_zero
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    (poitouCompactExplicitFormulaKernel y R hy hR).kernel 0 = 1 := by
  change poitouCompactRegularizedKernel y R 0 = 1
  simp [poitouCompactRegularizedKernel, hR.ne']

private def poitouCompactPositiveEndpoint (y R x : ℝ) : ℝ :=
  poitouCompactRegularizedKernel y R x * Real.exp (x / 2)

private def poitouCompactNegativeEndpoint (y R x : ℝ) : ℝ :=
  poitouCompactRegularizedKernel y R x * Real.exp (-x / 2)

private theorem poitouCompactPositiveEndpoint_integrable
    (y : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (poitouCompactPositiveEndpoint y R) volume := by
  have hs : HasCompactSupport (poitouCompactRegularizedKernel y R) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(8 * R)) (8 * R)) isCompact_Icc
    intro x hx
    change -(8 * R) ≤ x ∧ x ≤ 8 * R
    rw [← abs_le]
    by_contra hbound
    exact hx (poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs
      hR (lt_of_not_ge hbound))
  exact ((poitouCompactRegularizedKernel_continuous hR).mul
    (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hs.mul_right

private theorem poitouCompactNegativeEndpoint_integrable
    (y : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (poitouCompactNegativeEndpoint y R) volume := by
  have hs : HasCompactSupport (poitouCompactRegularizedKernel y R) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(8 * R)) (8 * R)) isCompact_Icc
    intro x hx
    change -(8 * R) ≤ x ∧ x ≤ 8 * R
    rw [← abs_le]
    by_contra hbound
    exact hx (poitouCompactRegularizedKernel_eq_zero_of_radius_lt_abs
      hR (lt_of_not_ge hbound))
  exact ((poitouCompactRegularizedKernel_continuous hR).mul
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).integrable_of_hasCompactSupport
      hs.mul_right

private theorem poitouCompactPhi_one_eq_endpoint
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    (poitouCompactExplicitFormulaKernel y R hy hR).phi 1 =
      (((∫ x : ℝ, poitouCompactPositiveEndpoint y R x) : ℝ) : ℂ) := by
  unfold TraceEuclidean.CompactExplicitFormulaKernel.phi
  change (∫ x : ℝ, (poitouCompactRegularizedKernel y R x : ℂ) *
      Complex.exp (((1 : ℂ) - 1 / 2) * (x : ℂ))) = _
  calc
    _ = ∫ x : ℝ, (poitouCompactPositiveEndpoint y R x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((1 : ℂ) - 1 / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (x / 2)).symm]
      simp [poitouCompactPositiveEndpoint]
    _ = _ := integral_ofReal

private theorem poitouCompactPhi_zero_eq_endpoint
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    (poitouCompactExplicitFormulaKernel y R hy hR).phi 0 =
      (((∫ x : ℝ, poitouCompactNegativeEndpoint y R x) : ℝ) : ℂ) := by
  unfold TraceEuclidean.CompactExplicitFormulaKernel.phi
  change (∫ x : ℝ, (poitouCompactRegularizedKernel y R x : ℂ) *
      Complex.exp (((0 : ℂ) - 1 / 2) * (x : ℂ))) = _
  calc
    _ = ∫ x : ℝ, (poitouCompactNegativeEndpoint y R x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((0 : ℂ) - 1 / 2) * (x : ℂ) = ((-x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (-x / 2)).symm]
      simp [poitouCompactNegativeEndpoint]
    _ = _ := integral_ofReal

private theorem poitouCompact_endpoint_pointwise (y R x : ℝ) :
    poitouCompactPositiveEndpoint y R x +
        poitouCompactNegativeEndpoint y R x =
      2 * (poitouScaledTest y x * poitouCompactCutoff R x) := by
  unfold poitouCompactPositiveEndpoint poitouCompactNegativeEndpoint
    poitouCompactRegularizedKernel poitouFullKernel
  rw [Real.cosh_eq]
  have hden : Real.exp (x / 2) + Real.exp (-(x / 2)) ≠ 0 := by positivity
  field_simp [hden]

private theorem poitouCompactScaledTest_integral_univ_eq_Ioi
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    (∫ x : ℝ, poitouScaledTest y x * poitouCompactCutoff R x) =
      2 * ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouCompactCutoff R x := by
  let f : ℝ → ℝ := fun x ↦
    poitouScaledTest y x * poitouCompactCutoff R x
  have heven (x : ℝ) : f |x| = f x := by
    dsimp only [f]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, poitouScaledTest_even,
        poitouCompactCutoff_even]
  calc
    (∫ x : ℝ, poitouScaledTest y x * poitouCompactCutoff R x) =
        ∫ x : ℝ, f |x| := by
      apply integral_congr_ae
      filter_upwards with x
      exact (heven x).symm
    _ = 2 * ∫ x in Ioi (0 : ℝ), f x := integral_comp_abs
    _ = _ := rfl

/-- Exact endpoint identity for every positive compact radius. -/
theorem poitouCompactPhi_zero_add_one
    {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    (poitouCompactExplicitFormulaKernel y R hy hR).phi 0 +
        (poitouCompactExplicitFormulaKernel y R hy hR).phi 1 =
      ((4 * ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouCompactCutoff R x : ℝ) : ℂ) := by
  rw [poitouCompactPhi_zero_eq_endpoint hy hR,
    poitouCompactPhi_one_eq_endpoint hy hR]
  rw [← ofReal_add]
  rw [add_comm (∫ x : ℝ, poitouCompactNegativeEndpoint y R x),
    ← integral_add (poitouCompactPositiveEndpoint_integrable y hR)
      (poitouCompactNegativeEndpoint_integrable y hR)]
  have hpoint : (fun x : ℝ ↦
      poitouCompactPositiveEndpoint y R x +
        poitouCompactNegativeEndpoint y R x) =
      fun x : ℝ ↦
        2 * (poitouScaledTest y x * poitouCompactCutoff R x) := by
    funext x
    exact poitouCompact_endpoint_pointwise y R x
  rw [hpoint, integral_const_mul,
    poitouCompactScaledTest_integral_univ_eq_Ioi hy hR]
  push_cast
  ring

/-- The compact endpoint area converges to the unregularized Poitou area. -/
theorem poitouCompactScaledTest_integral_Ioi_tendsto
    {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouCompactCutoff ((n : ℝ) + 1) x)
      atTop (𝓝 (3 * Real.pi / (5 * Real.sqrt y))) := by
  have hDCT : Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouCompactCutoff ((n : ℝ) + 1) x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), poitouScaledTest y x)) := by
    apply tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (fun x : ℝ ↦ poitouScaledTest y x)
    · intro n
      exact ((poitouScaledTest_continuous y).mul
        (poitouCompactCutoff_continuous (by positivity))).aestronglyMeasurable
    · exact (poitouScaledTest_integrable hy).integrableOn
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (poitouScaledTest_nonneg y x)
          (poitouCompactCutoff_nonneg _ x))]
      exact mul_le_of_le_one_right (poitouScaledTest_nonneg y x)
        (poitouCompactCutoff_le_one _ x)
    · filter_upwards with x
      simpa using (tendsto_const_nhds.mul (poitouCompactCutoff_tendsto_one x))
  simpa only [poitouScaledTest_integral_Ioi hy] using hDCT

/-- The two endpoint residues converge to `12π/(5√y)`. -/
theorem poitouCompactPhi_zero_add_one_tendsto
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ ↦
      let R : ℝ := (n : ℝ) + 1
      let hR : 0 < R := by positivity
      (poitouCompactExplicitFormulaKernel y R hy hR).phi 0 +
        (poitouCompactExplicitFormulaKernel y R hy hR).phi 1)
      atTop (𝓝 ((12 * Real.pi / (5 * Real.sqrt y) : ℝ) : ℂ)) := by
  have h := (poitouCompactScaledTest_integral_Ioi_tendsto hy).const_mul 4
  have hc := h.ofReal
  convert hc using 1
  · funext n
    dsimp only
    rw [poitouCompactPhi_zero_add_one hy (by positivity)]
  · push_cast
    congr 1
    ring

/-- The hyperbolic kernel in Poitou's totally real correction. -/
def poitouTotallyRealArchKernel (x : ℝ) : ℝ :=
  1 / Real.sinh x + 1 / (2 * Real.cosh (x / 2) ^ 2)

private def poitouCutoffDelta : ℝ := 1 / 100

private def poitouCutoffLocalA : ℝ :=
  (9 / 2) * poitouCutoffDelta + Real.sinh (poitouCutoffDelta / 2)

private def poitouCutoffLocalBound : ℝ :=
  poitouCutoffLocalA * (1 + poitouCutoffDelta / 2)

private def poitouCutoffTailBound : ℝ :=
  2 / (1 - Real.exp (-2 * poitouCutoffDelta)) + 2

private def poitouCutoffMajorantConstant : ℝ :=
  poitouCutoffLocalBound * Real.exp poitouCutoffDelta +
    poitouCutoffTailBound

private theorem poitouCutoffDelta_pos : 0 < poitouCutoffDelta := by
  norm_num [poitouCutoffDelta]

private theorem poitouCutoffLocalA_nonneg : 0 ≤ poitouCutoffLocalA := by
  unfold poitouCutoffLocalA
  have hdelta : 0 ≤ poitouCutoffDelta := poitouCutoffDelta_pos.le
  have hs : 0 ≤ Real.sinh (poitouCutoffDelta / 2) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg hdelta (by norm_num))
  exact add_nonneg (mul_nonneg (by norm_num) hdelta) hs

private theorem poitouCutoffLocalBound_nonneg : 0 ≤ poitouCutoffLocalBound := by
  unfold poitouCutoffLocalBound
  exact mul_nonneg poitouCutoffLocalA_nonneg
    (add_nonneg (by norm_num)
      (div_nonneg poitouCutoffDelta_pos.le (by norm_num)))

private theorem poitouCutoffTailDen_pos :
    0 < 1 - Real.exp (-2 * poitouCutoffDelta) := by
  have h := Real.exp_lt_one_iff.mpr (by
    have := poitouCutoffDelta_pos
    linarith : -2 * poitouCutoffDelta < 0)
  linarith

private theorem poitouCutoffTailBound_nonneg : 0 ≤ poitouCutoffTailBound := by
  unfold poitouCutoffTailBound
  exact add_nonneg
    (div_nonneg (by norm_num) poitouCutoffTailDen_pos.le) (by norm_num)

private theorem poitouCutoffMajorantConstant_nonneg :
    0 ≤ poitouCutoffMajorantConstant := by
  unfold poitouCutoffMajorantConstant
  exact add_nonneg
    (mul_nonneg poitouCutoffLocalBound_nonneg (Real.exp_pos _).le)
    poitouCutoffTailBound_nonneg

theorem poitouTotallyRealArchKernel_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ poitouTotallyRealArchKernel x := by
  unfold poitouTotallyRealArchKernel
  exact add_nonneg
    (div_nonneg zero_le_one (Real.sinh_pos_iff.mpr hx).le)
    (div_nonneg zero_le_one
      (mul_nonneg (by norm_num) (sq_nonneg (Real.cosh (x / 2)))))

/-- Away from the origin, the hyperbolic kernel has a uniform exponential
majorant. -/
theorem poitouTotallyRealArchKernel_le_exp {x : ℝ}
    (hx : poitouCutoffDelta ≤ x) :
    poitouTotallyRealArchKernel x ≤
      poitouCutoffTailBound * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le poitouCutoffDelta_pos hx
  have hden0 : 0 < 1 - Real.exp (-2 * x) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith : -2 * x < 0)
    linarith
  have hden :
      1 - Real.exp (-2 * poitouCutoffDelta) ≤
        1 - Real.exp (-2 * x) := by
    have he : Real.exp (-2 * x) ≤
        Real.exp (-2 * poitouCutoffDelta) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsinhId :
      1 / Real.sinh x =
        2 * Real.exp (-x) / (1 - Real.exp (-2 * x)) := by
    have hexp : Real.exp (-x) =
        Real.exp x * Real.exp (-2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.sinh_eq, hexp]
    have hexp0 : Real.exp x ≠ 0 := Real.exp_ne_zero x
    field_simp [hexp0, hden0.ne']
    have hprod : Real.exp x ^ 2 * Real.exp (-(2 * x)) = 1 := by
      calc
        Real.exp x ^ 2 * Real.exp (-(2 * x)) =
            Real.exp (x + x) * Real.exp (-(2 * x)) := by
              rw [pow_two, ← Real.exp_add]
        _ = Real.exp ((x + x) + -(2 * x)) := by rw [← Real.exp_add]
        _ = 1 := by
          rw [show (x + x) + -(2 * x) = 0 by ring]
          exact Real.exp_zero
    rw [hprod]
  have hsinhBound :
      1 / Real.sinh x ≤
        (2 / (1 - Real.exp (-2 * poitouCutoffDelta))) *
          Real.exp (-x) := by
    rw [hsinhId]
    calc
      2 * Real.exp (-x) / (1 - Real.exp (-2 * x)) ≤
          2 * Real.exp (-x) /
            (1 - Real.exp (-2 * poitouCutoffDelta)) :=
        div_le_div_of_nonneg_left (by positivity)
          poitouCutoffTailDen_pos hden
      _ = _ := by ring
  have hcoshLower : Real.exp (x / 2) / 2 ≤ Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(x / 2))]
  have hsq : Real.exp x / 4 ≤ Real.cosh (x / 2) ^ 2 := by
    have hmul := mul_self_le_mul_self (by positivity : 0 ≤ Real.exp (x / 2) / 2)
      hcoshLower
    rw [← pow_two, ← pow_two] at hmul
    calc
      Real.exp x / 4 = (Real.exp (x / 2) / 2) ^ 2 := by
        rw [div_pow]
        norm_num
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.cosh (x / 2) ^ 2 := hmul
  have hcoshBound :
      1 / (2 * Real.cosh (x / 2) ^ 2) ≤ 2 * Real.exp (-x) := by
    have hdenLower : Real.exp x / 2 ≤ 2 * Real.cosh (x / 2) ^ 2 := by
      nlinarith [hsq]
    calc
      1 / (2 * Real.cosh (x / 2) ^ 2) ≤ 1 / (Real.exp x / 2) :=
        one_div_le_one_div_of_le (by positivity) hdenLower
      _ = 2 * Real.exp (-x) := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
  unfold poitouTotallyRealArchKernel poitouCutoffTailBound
  calc
    1 / Real.sinh x + 1 / (2 * Real.cosh (x / 2) ^ 2) ≤
        (2 / (1 - Real.exp (-2 * poitouCutoffDelta))) * Real.exp (-x) +
          2 * Real.exp (-x) := add_le_add hsinhBound hcoshBound
    _ = (2 / (1 - Real.exp (-2 * poitouCutoffDelta)) + 2) *
          Real.exp (-x) := by ring

/-- The positive-half-line correction attached to a compact Poitou cutoff. -/
def poitouCompactArchCorrection (R x : ℝ) : ℝ :=
  (1 - poitouScaledTest poitouY x * poitouCompactCutoff R x) *
    poitouTotallyRealArchKernel x

/-- The correction after removal of the compact cutoff. -/
def poitouArchCorrection (x : ℝ) : ℝ :=
  (1 - poitouScaledTest poitouY x) * poitouTotallyRealArchKernel x

private theorem poitouCompactCutoff_one_sub_le_local
    {R x : ℝ} (hR : 1 ≤ R) (hx0 : 0 ≤ x)
    (hxδ : x ≤ poitouCutoffDelta) :
    1 - poitouCompactCutoff R x ≤
      x * Real.sinh (poitouCutoffDelta / 2) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hx : x = 0
  · subst x
    simp [poitouCompactCutoff, hRpos.ne', TraceEuclidean.odlyzkoF4_zero]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hu0 : 0 ≤ x / R := div_nonneg hx0 hRpos.le
  have hux : x / R ≤ x := div_le_self hx0 hR
  have huδ : x / R ≤ (1 / 100 : ℝ) := by
    simpa [poitouCutoffDelta] using hux.trans hxδ
  have hsource := TraceEuclidean.odlyzkoSinhIntegrand_le_half_x hu0 huδ
  have hden : 0 < 2 * Real.sinh ((x / R) / 2) := by
    have : 0 < (x / R) / 2 := by positivity
    exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr this)
  have hraw :
      1 - TraceEuclidean.odlyzkoF4 (x / R) ≤
        (x / R) * Real.sinh ((x / R) / 2) := by
    have hmul := (div_le_iff₀ hden).mp hsource
    nlinarith
  have hsinh : Real.sinh ((x / R) / 2) ≤
      Real.sinh (poitouCutoffDelta / 2) := by
    rw [Real.sinh_le_sinh]
    linarith [hux]
  have hsinh0 : 0 ≤ Real.sinh ((x / R) / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hprod :
      (x / R) * Real.sinh ((x / R) / 2) ≤
        x * Real.sinh (poitouCutoffDelta / 2) :=
    mul_le_mul hux hsinh hsinh0 hx0
  exact hraw.trans hprod

private theorem poitouCompactArchNumerator_nonneg
    (R x : ℝ) :
    0 ≤ 1 - poitouScaledTest poitouY x * poitouCompactCutoff R x := by
  have hf0 := poitouScaledTest_nonneg poitouY x
  have hf1 : poitouScaledTest poitouY x ≤ 1 :=
    sub_nonneg.mp (poitouOneSubScaled_bounds poitouY x).1
  have hfc : poitouScaledTest poitouY x * poitouCompactCutoff R x ≤
      poitouScaledTest poitouY x :=
    mul_le_of_le_one_right hf0 (poitouCompactCutoff_le_one R x)
  exact sub_nonneg.mpr (hfc.trans hf1)

private theorem poitouCompactArchNumerator_le_local
    {R x : ℝ} (hR : 1 ≤ R) (hx0 : 0 ≤ x)
    (hxδ : x ≤ poitouCutoffDelta) :
    1 - poitouScaledTest poitouY x * poitouCompactCutoff R x ≤
      x * poitouCutoffLocalA := by
  let f := poitouScaledTest poitouY x
  let c := poitouCompactCutoff R x
  have hf0 : 0 ≤ f := poitouScaledTest_nonneg poitouY x
  have hf1 : f ≤ 1 := sub_nonneg.mp (poitouOneSubScaled_bounds poitouY x).1
  have hc0 : 0 ≤ 1 - c := sub_nonneg.mpr (poitouCompactCutoff_le_one R x)
  have hquad : 1 - f ≤ (9 / 2 : ℝ) * x ^ 2 := by
    have h := poitouScaledTest_one_sub_abs_le x
    have hle : 1 - f ≤ |1 - f| := le_abs_self (1 - f)
    simpa [f, abs_of_nonneg hx0] using hle.trans h
  have hcut : 1 - c ≤ x * Real.sinh (poitouCutoffDelta / 2) := by
    simpa [c] using poitouCompactCutoff_one_sub_le_local hR hx0 hxδ
  have hcutTerm : f * (1 - c) ≤
      x * Real.sinh (poitouCutoffDelta / 2) := by
    calc
      f * (1 - c) ≤ 1 * (x * Real.sinh (poitouCutoffDelta / 2)) :=
        mul_le_mul hf1 hcut hc0 zero_le_one
      _ = _ := by ring
  have hinner :
      (9 / 2 : ℝ) * x + Real.sinh (poitouCutoffDelta / 2) ≤
        (9 / 2 : ℝ) * poitouCutoffDelta +
          Real.sinh (poitouCutoffDelta / 2) := by
    nlinarith
  calc
    1 - f * c = (1 - f) + f * (1 - c) := by ring
    _ ≤ (9 / 2 : ℝ) * x ^ 2 +
        x * Real.sinh (poitouCutoffDelta / 2) :=
      add_le_add hquad hcutTerm
    _ = x * ((9 / 2 : ℝ) * x +
        Real.sinh (poitouCutoffDelta / 2)) := by ring
    _ ≤ x * ((9 / 2 : ℝ) * poitouCutoffDelta +
        Real.sinh (poitouCutoffDelta / 2)) :=
      mul_le_mul_of_nonneg_left hinner hx0
    _ = x * poitouCutoffLocalA := by rfl

theorem poitouCompactArchCorrection_nonneg
    {R x : ℝ} (hx : 0 < x) :
    0 ≤ poitouCompactArchCorrection R x := by
  unfold poitouCompactArchCorrection
  exact mul_nonneg (poitouCompactArchNumerator_nonneg R x)
    (poitouTotallyRealArchKernel_nonneg hx)

private theorem poitouCompactArchCorrection_le_local
    {R x : ℝ} (hR : 1 ≤ R) (hx : 0 < x)
    (hxδ : x ≤ poitouCutoffDelta) :
    poitouCompactArchCorrection R x ≤ poitouCutoffLocalBound := by
  let N : ℝ := 1 -
    poitouScaledTest poitouY x * poitouCompactCutoff R x
  have hN0 : 0 ≤ N := poitouCompactArchNumerator_nonneg R x
  have hN : N ≤ x * poitouCutoffLocalA := by
    simpa [N] using poitouCompactArchNumerator_le_local hR hx.le hxδ
  have hsinhPos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hxsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hfirst : N / Real.sinh x ≤ poitouCutoffLocalA := by
    apply (div_le_iff₀ hsinhPos).2
    calc
      N ≤ x * poitouCutoffLocalA := hN
      _ ≤ Real.sinh x * poitouCutoffLocalA :=
        mul_le_mul_of_nonneg_right hxsinh poitouCutoffLocalA_nonneg
      _ = poitouCutoffLocalA * Real.sinh x := by ring
  have hcoshSq : 1 ≤ Real.cosh (x / 2) ^ 2 := by
    nlinarith [Real.one_le_cosh (x / 2)]
  have hden : (2 : ℝ) ≤ 2 * Real.cosh (x / 2) ^ 2 := by nlinarith
  have hsecond :
      N / (2 * Real.cosh (x / 2) ^ 2) ≤
        poitouCutoffDelta * poitouCutoffLocalA / 2 := by
    calc
      N / (2 * Real.cosh (x / 2) ^ 2) ≤ N / 2 :=
        div_le_div_of_nonneg_left hN0 (by norm_num) hden
      _ ≤ (x * poitouCutoffLocalA) / 2 :=
        div_le_div_of_nonneg_right hN (by norm_num)
      _ ≤ (poitouCutoffDelta * poitouCutoffLocalA) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hxδ poitouCutoffLocalA_nonneg
  unfold poitouCompactArchCorrection poitouTotallyRealArchKernel
  change N * (1 / Real.sinh x +
      1 / (2 * Real.cosh (x / 2) ^ 2)) ≤ poitouCutoffLocalBound
  rw [mul_add, mul_one_div, mul_one_div]
  unfold poitouCutoffLocalBound
  nlinarith

private theorem poitouCompactArchCorrection_le_tail
    {R x : ℝ} (hx : poitouCutoffDelta ≤ x) :
    poitouCompactArchCorrection R x ≤
      poitouCutoffTailBound * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le poitouCutoffDelta_pos hx
  let N : ℝ := 1 -
    poitouScaledTest poitouY x * poitouCompactCutoff R x
  have hN0 : 0 ≤ N := poitouCompactArchNumerator_nonneg R x
  have hN1 : N ≤ 1 := by
    dsimp only [N]
    have hprod : 0 ≤
        poitouScaledTest poitouY x * poitouCompactCutoff R x :=
      mul_nonneg (poitouScaledTest_nonneg poitouY x)
        (poitouCompactCutoff_nonneg R x)
    linarith
  have hkernel0 := poitouTotallyRealArchKernel_nonneg hxpos
  unfold poitouCompactArchCorrection
  change N * poitouTotallyRealArchKernel x ≤ _
  calc
    N * poitouTotallyRealArchKernel x ≤
        1 * poitouTotallyRealArchKernel x :=
      mul_le_mul_of_nonneg_right hN1 hkernel0
    _ = poitouTotallyRealArchKernel x := one_mul _
    _ ≤ poitouCutoffTailBound * Real.exp (-x) :=
      poitouTotallyRealArchKernel_le_exp hx

/-- A single integrable exponential majorizes every compact correction once
the cutoff radius is at least one. -/
theorem poitouCompactArchCorrection_le_majorant
    {R x : ℝ} (hR : 1 ≤ R) (hx : 0 < x) :
    poitouCompactArchCorrection R x ≤
      poitouCutoffMajorantConstant * Real.exp (-x) := by
  rcases le_total x poitouCutoffDelta with hxδ | hxδ
  · have hlocal := poitouCompactArchCorrection_le_local hR hx hxδ
    have hexpFactor : 1 ≤
        Real.exp poitouCutoffDelta * Real.exp (-x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hscaled : poitouCutoffLocalBound ≤
        poitouCutoffLocalBound * Real.exp poitouCutoffDelta *
          Real.exp (-x) := by
      calc
        poitouCutoffLocalBound = poitouCutoffLocalBound * 1 := by ring
        _ ≤ poitouCutoffLocalBound *
            (Real.exp poitouCutoffDelta * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left hexpFactor
            poitouCutoffLocalBound_nonneg
        _ = _ := by ring
    calc
      poitouCompactArchCorrection R x ≤ poitouCutoffLocalBound := hlocal
      _ ≤ poitouCutoffLocalBound * Real.exp poitouCutoffDelta *
          Real.exp (-x) := hscaled
      _ ≤ poitouCutoffMajorantConstant * Real.exp (-x) := by
        unfold poitouCutoffMajorantConstant
        have htail : 0 ≤ poitouCutoffTailBound * Real.exp (-x) :=
          mul_nonneg poitouCutoffTailBound_nonneg (Real.exp_pos _).le
        nlinarith
  · have htail := poitouCompactArchCorrection_le_tail (R := R) hxδ
    calc
      poitouCompactArchCorrection R x ≤
          poitouCutoffTailBound * Real.exp (-x) := htail
      _ ≤ poitouCutoffMajorantConstant * Real.exp (-x) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        unfold poitouCutoffMajorantConstant
        exact le_add_of_nonneg_left
          (mul_nonneg poitouCutoffLocalBound_nonneg
            (Real.exp_pos _).le)

theorem poitouCompactArchCorrection_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ ↦ poitouCompactArchCorrection ((n : ℝ) + 1) x)
      atTop (𝓝 (poitouArchCorrection x)) := by
  have hc := poitouCompactCutoff_tendsto_one x
  have hp : Tendsto
      (fun n : ℕ ↦ poitouScaledTest poitouY x *
        poitouCompactCutoff ((n : ℝ) + 1) x)
      atTop (𝓝 (poitouScaledTest poitouY x * 1)) :=
    tendsto_const_nhds.mul hc
  have hn : Tendsto
      (fun n : ℕ ↦ 1 - poitouScaledTest poitouY x *
        poitouCompactCutoff ((n : ℝ) + 1) x)
      atTop (𝓝 (1 - poitouScaledTest poitouY x * 1)) :=
    tendsto_const_nhds.sub hp
  have hm := hn.mul_const (poitouTotallyRealArchKernel x)
  simpa [poitouCompactArchCorrection, poitouArchCorrection] using hm

private theorem poitouCompactArchCorrection_aestronglyMeasurable
    (R : ℝ) :
    AEStronglyMeasurable (poitouCompactArchCorrection R) volume := by
  apply Measurable.aestronglyMeasurable
  unfold poitouCompactArchCorrection poitouTotallyRealArchKernel
  have hf : Measurable (poitouScaledTest poitouY) :=
    (poitouScaledTest_continuous poitouY).measurable
  have hc : Measurable (poitouCompactCutoff R) := by
    unfold poitouCompactCutoff
    exact TraceEuclidean.odlyzkoF4_continuous.measurable.comp
      (continuous_id.div_const R).measurable
  have hs : Measurable (fun x : ℝ ↦ Real.sinh x) :=
    Real.continuous_sinh.measurable
  have hh : Measurable (fun x : ℝ ↦ Real.cosh (x / 2)) :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable
  exact (measurable_const.sub (hf.mul hc)).mul
    ((measurable_const.div hs).add
      (measurable_const.div
        (measurable_const.mul (hh.pow_const 2))))

private theorem poitouCutoffMajorant_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ poitouCutoffMajorantConstant * Real.exp (-x))
      (Ioi 0) :=
  (integrableOn_exp_neg_Ioi 0).const_mul poitouCutoffMajorantConstant

/-- Dominated convergence removes the compact cutoff in the full totally real
archimedean correction. -/
theorem poitouCompactArchCorrection_integral_tendsto :
    Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouCompactArchCorrection ((n : ℝ) + 1) x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), poitouArchCorrection x)) := by
  apply tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (fun x : ℝ ↦ poitouCutoffMajorantConstant * Real.exp (-x))
  · intro n
    exact (poitouCompactArchCorrection_aestronglyMeasurable
      ((n : ℝ) + 1)).mono_measure Measure.restrict_le_self
  · exact poitouCutoffMajorant_integrableOn
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (poitouCompactArchCorrection_nonneg hx)]
    exact poitouCompactArchCorrection_le_majorant (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) hx
  · filter_upwards with x
    exact poitouCompactArchCorrection_tendsto x

private theorem poitouArchCorrection_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ poitouArchCorrection x := by
  unfold poitouArchCorrection
  exact mul_nonneg (poitouOneSubScaled_bounds poitouY x).1
    (poitouTotallyRealArchKernel_nonneg hx)

private theorem poitouArchCorrection_le_compact_one {x : ℝ} (hx : 0 < x) :
    poitouArchCorrection x ≤ poitouCompactArchCorrection 1 x := by
  have hf0 := poitouScaledTest_nonneg poitouY x
  have hc1 := poitouCompactCutoff_le_one (1 : ℝ) x
  have hnum : 1 - poitouScaledTest poitouY x ≤
      1 - poitouScaledTest poitouY x * poitouCompactCutoff 1 x := by
    have hprod : poitouScaledTest poitouY x * poitouCompactCutoff 1 x ≤
        poitouScaledTest poitouY x :=
      mul_le_of_le_one_right hf0 hc1
    linarith
  unfold poitouArchCorrection poitouCompactArchCorrection
  exact mul_le_mul_of_nonneg_right hnum
    (poitouTotallyRealArchKernel_nonneg hx)

private theorem poitouArchCorrection_aestronglyMeasurable :
    AEStronglyMeasurable poitouArchCorrection volume := by
  apply Measurable.aestronglyMeasurable
  unfold poitouArchCorrection poitouTotallyRealArchKernel
  have hf : Measurable (poitouScaledTest poitouY) :=
    (poitouScaledTest_continuous poitouY).measurable
  have hs : Measurable (fun x : ℝ ↦ Real.sinh x) :=
    Real.continuous_sinh.measurable
  have hh : Measurable (fun x : ℝ ↦ Real.cosh (x / 2)) :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable
  exact (measurable_const.sub hf).mul
    ((measurable_const.div hs).add
      (measurable_const.div
        (measurable_const.mul (hh.pow_const 2))))

private theorem poitouArchCorrection_integrableOn :
    IntegrableOn poitouArchCorrection (Ioi 0) := by
  apply poitouCutoffMajorant_integrableOn.mono'
  · exact poitouArchCorrection_aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (poitouArchCorrection_nonneg hx)]
    exact (poitouArchCorrection_le_compact_one hx).trans
      (poitouCompactArchCorrection_le_majorant (R := (1 : ℝ)) le_rfl hx)

private theorem poitouSinhCorrection_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ (1 - poitouScaledTest poitouY x) / Real.sinh x)
      (Ioi 0) := by
  apply poitouArchCorrection_integrableOn.mono'
  · apply Measurable.aestronglyMeasurable
    exact (measurable_const.sub
      (poitouScaledTest_continuous poitouY).measurable).div
        Real.continuous_sinh.measurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnum := (poitouOneSubScaled_bounds poitouY x).1
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hterm0 : 0 ≤
        (1 - poitouScaledTest poitouY x) / Real.sinh x :=
      div_nonneg hnum hsinh.le
    have hother0 : 0 ≤
        (1 - poitouScaledTest poitouY x) /
          (2 * Real.cosh (x / 2) ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
    unfold poitouArchCorrection poitouTotallyRealArchKernel
    rw [mul_add, mul_one_div, mul_one_div]
    exact le_add_of_nonneg_right hother0

private theorem poitouCoshCorrection_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ (1 - poitouScaledTest poitouY x) /
        (2 * Real.cosh (x / 2) ^ 2))
      (Ioi 0) := by
  apply poitouArchCorrection_integrableOn.mono'
  · apply Measurable.aestronglyMeasurable
    have hh : Measurable (fun x : ℝ ↦ Real.cosh (x / 2)) :=
      (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable
    exact (measurable_const.sub
      (poitouScaledTest_continuous poitouY).measurable).div
        (measurable_const.mul (hh.pow_const 2))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnum := (poitouOneSubScaled_bounds poitouY x).1
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hterm0 : 0 ≤
        (1 - poitouScaledTest poitouY x) /
          (2 * Real.cosh (x / 2) ^ 2) := by positivity
    have hother0 : 0 ≤
        (1 - poitouScaledTest poitouY x) / Real.sinh x :=
      div_nonneg hnum hsinh.le
    rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
    unfold poitouArchCorrection poitouTotallyRealArchKernel
    rw [mul_add, mul_one_div, mul_one_div]
    exact le_add_of_nonneg_left hother0

/-- The limiting correction is exactly the two-integral quantity appearing in
Poitou's equation (24). -/
theorem poitouArchCorrection_integral_eq :
    (∫ x in Ioi (0 : ℝ), poitouArchCorrection x) =
      poitouCorrectionIntegral poitouY := by
  unfold poitouCorrectionIntegral
  rw [← integral_add poitouSinhCorrection_integrableOn
    poitouCoshCorrection_integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  unfold poitouArchCorrection poitouTotallyRealArchKernel
  ring

theorem poitouCompactArchCorrection_integral_tendsto_correctionIntegral :
    Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouCompactArchCorrection ((n : ℝ) + 1) x)
      atTop (𝓝 (poitouCorrectionIntegral poitouY)) := by
  simpa only [poitouArchCorrection_integral_eq] using
    poitouCompactArchCorrection_integral_tendsto

private def poitouRealElementaryKernel (x : ℝ) : ℝ :=
  2 / (Real.exp x + 1) +
    2 * Real.exp x / (Real.exp x + 1) ^ 2

private theorem poitouRealSecondElementary_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ 2 * Real.exp x / (Real.exp x + 1) ^ 2)
      (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul 2).mono'
  · exact ((Real.continuous_exp.const_mul 2).div
      ((Real.continuous_exp.add continuous_const).pow 2)
      (fun x ↦ (sq_pos_of_pos
        (add_pos (Real.exp_pos x) zero_lt_one)).ne')).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), Real.exp_neg]
    have he : 0 < Real.exp x := Real.exp_pos x
    have hsum : 0 < Real.exp x + 1 := add_pos he zero_lt_one
    apply (div_le_div_iff₀ (sq_pos_of_pos hsum) he).2
    nlinarith [sq_nonneg (Real.exp x + 1)]

private theorem poitouRealSecondElementary_integral :
    (∫ x in Ioi (0 : ℝ),
      2 * Real.exp x / (Real.exp x + 1) ^ 2) = 1 := by
  let F : ℝ → ℝ := fun x ↦ -2 * (Real.exp x + 1)⁻¹
  have hderiv (x : ℝ) :
      HasDerivAt F (2 * Real.exp x / (Real.exp x + 1) ^ 2) x := by
    have hden := (Real.hasDerivAt_exp x).add_const 1
    have hraw := (hden.inv (by positivity)).const_mul (-2 : ℝ)
    dsimp only [F]
    convert hraw using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hlogistic : Tendsto
      (fun x : ℝ ↦ 1 / (Real.exp x + 1)) atTop (𝓝 0) := by
    have hnonneg (x : ℝ) : 0 ≤ 1 / (Real.exp x + 1) := by positivity
    have hle (x : ℝ) :
        1 / (Real.exp x + 1) ≤ Real.exp (-x) := by
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le
        (Real.exp_pos x) (by linarith : Real.exp x ≤ Real.exp x + 1)
    exact squeeze_zero hnonneg hle Real.tendsto_exp_neg_atTop_nhds_zero
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa [F] using
      hlogistic.const_mul (-2 : ℝ)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ hderiv x) poitouRealSecondElementary_integrableOn hlim]
  norm_num [F]

private theorem poitouRealElementaryKernel_integrableOn :
    IntegrableOn poitouRealElementaryKernel (Ioi 0) := by
  have h := (TraceEuclidean.odlyzkoLogistic_integrableOn.const_mul 2).add
    poitouRealSecondElementary_integrableOn
  apply h.congr
  filter_upwards with x
  unfold poitouRealElementaryKernel
  simp only [Pi.add_apply]
  ring

private theorem poitouRealElementaryKernel_integral :
    (∫ x in Ioi (0 : ℝ), poitouRealElementaryKernel x) =
      2 * Real.log 2 + 1 := by
  calc
    (∫ x in Ioi (0 : ℝ), poitouRealElementaryKernel x) =
        ∫ x in Ioi (0 : ℝ),
          2 * (1 / (Real.exp x + 1)) +
            2 * Real.exp x / (Real.exp x + 1) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      unfold poitouRealElementaryKernel
      ring
    _ = (∫ x in Ioi (0 : ℝ), 2 * (1 / (Real.exp x + 1))) +
        ∫ x in Ioi (0 : ℝ),
          2 * Real.exp x / (Real.exp x + 1) ^ 2 := by
      rw [integral_add
        (TraceEuclidean.odlyzkoLogistic_integrableOn.const_mul 2)
        poitouRealSecondElementary_integrableOn]
    _ = 2 * Real.log 2 + 1 := by
      rw [integral_const_mul, TraceEuclidean.odlyzkoLogistic_integral,
        poitouRealSecondElementary_integral]

private theorem poitouRealGaussKernel_algebra
    (z : ℝ) {x : ℝ} (hx : 0 < x) :
    2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        (z / Real.cosh (x / 2))) / (1 - Real.exp (-2 * x)) =
      (1 - z) * poitouTotallyRealArchKernel x -
        poitouRealElementaryKernel x := by
  let q : ℝ := Real.exp (-(x / 2))
  have hq0 : q ≠ 0 := by dsimp [q]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq4 : 1 - q ^ 4 ≠ 0 := by
    intro h
    have hq4eq : q ^ 4 = 1 := by linarith
    have hq2lt : q ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (q ^ 2 - 1)]
  have hq2add : 1 + q ^ 2 ≠ 0 := by positivity
  have hnegHalf : Real.exp (-(1 / 2 : ℝ) * x) = q := by
    dsimp [q]
    congr 1
    ring
  have hneg : Real.exp (-x) = q ^ 2 := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegTwo : Real.exp (-2 * x) = q ^ 4 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add, hneg]
    ring
  have hposHalf : Real.exp (x / 2) = q⁻¹ := by
    calc
      Real.exp (x / 2) = Real.exp (-(-(x / 2))) := by congr 1; ring
      _ = (Real.exp (-(x / 2)))⁻¹ := Real.exp_neg _
      _ = q⁻¹ := by rfl
  have hpos : Real.exp x = (q ^ 2)⁻¹ := by
    rw [show x = -(-x) by ring, Real.exp_neg, hneg]
  have hsinh : Real.sinh x = (1 - q ^ 4) / (2 * q ^ 2) := by
    rw [Real.sinh_eq, hpos, hneg]
    field_simp [hq0]
  have hcosh : Real.cosh (x / 2) = (1 + q ^ 2) / (2 * q) := by
    rw [Real.cosh_eq, hposHalf]
    change (q⁻¹ + q) / 2 = _
    field_simp [hq0]
  unfold poitouTotallyRealArchKernel poitouRealElementaryKernel
  rw [hnegTwo, hnegHalf, hsinh, hcosh, hpos]
  field_simp [hq0, hq4, hq2add]
  ring

theorem poitouCompactRealGaussIntegrand_eq
    {R x : ℝ} (hR : 0 < R) (hx : 0 < x) :
    2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        (poitouCompactExplicitFormulaKernel poitouY R (by
          norm_num [poitouY]) hR).kernel x) /
        (1 - Real.exp (-2 * x)) =
      poitouCompactArchCorrection R x - poitouRealElementaryKernel x := by
  change
    2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        poitouCompactRegularizedKernel poitouY R x) /
        (1 - Real.exp (-2 * x)) = _
  rw [show poitouCompactRegularizedKernel poitouY R x =
      (poitouScaledTest poitouY x * poitouCompactCutoff R x) /
        Real.cosh (x / 2) by
    unfold poitouCompactRegularizedKernel poitouFullKernel
    ring]
  exact poitouRealGaussKernel_algebra
    (poitouScaledTest poitouY x * poitouCompactCutoff R x) hx

private theorem poitouCompactArchCorrection_integrableOn
    {R : ℝ} (hR : 1 ≤ R) :
    IntegrableOn (poitouCompactArchCorrection R) (Ioi 0) := by
  apply poitouCutoffMajorant_integrableOn.mono'
  · exact (poitouCompactArchCorrection_aestronglyMeasurable R).mono_measure
      Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (poitouCompactArchCorrection_nonneg hx)]
    exact poitouCompactArchCorrection_le_majorant hR hx

/-- Exact real-place Gauss evaluation for every compact cutoff radius at least
one. -/
theorem poitouCompactRealGaussIntegral_eq
    {R : ℝ} (hR : 1 ≤ R) :
    (poitouCompactExplicitFormulaKernel poitouY R (by
      norm_num [poitouY]) (lt_of_lt_of_le zero_lt_one hR)).realGaussIntegral =
      (∫ x in Ioi (0 : ℝ), poitouCompactArchCorrection R x) -
        (2 * Real.log 2 + 1) := by
  let hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  unfold TraceEuclidean.CompactExplicitFormulaKernel.realGaussIntegral
  calc
    (∫ x in Ioi (0 : ℝ),
        2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
          (poitouCompactExplicitFormulaKernel poitouY R (by
            norm_num [poitouY]) hRpos).kernel x) /
          (1 - Real.exp (-2 * x))) =
        ∫ x in Ioi (0 : ℝ),
          (poitouCompactArchCorrection R x - poitouRealElementaryKernel x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact poitouCompactRealGaussIntegrand_eq hRpos hx
    _ = (∫ x in Ioi (0 : ℝ), poitouCompactArchCorrection R x) -
        ∫ x in Ioi (0 : ℝ), poitouRealElementaryKernel x := by
      rw [integral_sub (poitouCompactArchCorrection_integrableOn hR)
        poitouRealElementaryKernel_integrableOn]
    _ = _ := by rw [poitouRealElementaryKernel_integral]

/-- The compact real-place Gauss terms converge to Poitou's correction minus
the elementary constant. -/
theorem poitouCompactRealGaussIntegral_tendsto :
    Tendsto
      (fun n : ℕ ↦
        let R : ℝ := (n : ℝ) + 1
        let hR : 0 < R := by positivity
        (poitouCompactExplicitFormulaKernel poitouY R (by
          norm_num [poitouY]) hR).realGaussIntegral)
      atTop
      (𝓝 (poitouCorrectionIntegral poitouY - (2 * Real.log 2 + 1))) := by
  have h := poitouCompactArchCorrection_integral_tendsto_correctionIntegral.sub_const
    (2 * Real.log 2 + 1)
  convert h using 1
  funext n
  dsimp only
  rw [poitouCompactRealGaussIntegral_eq (by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)]

end PoitouKernel

end
end TraceEuclidean
