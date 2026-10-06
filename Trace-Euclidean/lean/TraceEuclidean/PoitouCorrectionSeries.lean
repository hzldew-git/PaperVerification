import TraceEuclidean.PoitouCorrectionIntegral
import TraceEuclidean.PoitouSeriesBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Poitou's archimedean correction series

This module proves the two hyperbolic-kernel expansions in Poitou's equation
(24), justifies interchange of the infinite sums with the positive-half-line
integrals, and identifies the source correction with the `poitouL1` series
used by the exact degree-eleven numerical certificate.
-/

namespace TraceEuclidean.PoitouKernel

open MeasureTheory Set Filter
open scoped BigOperators
open TraceEuclidean.PoitouDegreeEleven

noncomputable section
theorem poitouSinhKernel_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 2 * Real.exp (-(((2 * k + 1 : ℕ) : ℝ) * x)))
      (1 / Real.sinh x) := by
  let q : ℝ := Real.exp (-x)
  have hq0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq1 : q ^ 2 < 1 := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith
  have hsum := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * q)
  have hterms :
      (fun k : ℕ => 2 * Real.exp (-(((2 * k + 1 : ℕ) : ℝ) * x))) =
        (fun k : ℕ => 2 * q * (q ^ 2) ^ k) := by
    funext k
    dsimp only [q]
    rw [← pow_mul, ← Real.exp_nat_mul]
    rw [show -(((2 * k + 1 : ℕ) : ℝ) * x) =
      -x + (((2 * k : ℕ) : ℝ) * (-x)) by push_cast; ring, Real.exp_add]
    ring
  have hval : 1 / Real.sinh x = 2 * q * (1 - q ^ 2)⁻¹ := by
    dsimp only [q]
    rw [Real.sinh_eq, Real.exp_neg]
    have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    field_simp
  rw [hterms, hval]
  exact hsum


theorem poitouCoshKernel_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ =>
      2 * (-1 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * x)))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) := by
  let q : ℝ := Real.exp (-x)
  have hqAbs : ‖-q‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos (-x)).le]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsum :=
    (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hqAbs).mul_left (2 * q)
  have hterms :
      (fun k : ℕ =>
        2 * (-1 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * x))) =
      (fun k : ℕ =>
        2 * q * ((((k + 1).choose 1 : ℕ) : ℝ) * (-q) ^ k)) := by
    funext k
    rw [Nat.choose_one_right]
    dsimp only [q]
    have hexp : Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) =
        Real.exp (-x) * Real.exp (-x) ^ k := by
      rw [show -(((k + 1 : ℕ) : ℝ) * x) =
        -x + ((k : ℝ) * (-x)) by push_cast; ring, Real.exp_add,
        Real.exp_nat_mul]
    have hnegpow : (-Real.exp (-x)) ^ k =
        (-1 : ℝ) ^ k * Real.exp (-x) ^ k := by
      exact neg_pow _ _
    rw [hexp, hnegpow]
    ring
  have hval :
      1 / (2 * Real.cosh (x / 2) ^ 2) =
        2 * q * (1 / (1 - (-q)) ^ (1 + 1)) := by
    dsimp only [q]
    rw [Real.cosh_eq]
    let E : ℝ := Real.exp (x / 2)
    have he : E ≠ 0 := (Real.exp_pos _).ne'
    have hneg : Real.exp (-(x / 2)) = E⁻¹ := by
      dsimp only [E]
      exact Real.exp_neg _
    rw [hneg]
    have hsq : Real.exp x = E ^ 2 := by
      dsimp only [E]
      calc
        Real.exp x = Real.exp (x / 2 + x / 2) := by congr 1 <;> ring
        _ = Real.exp (x / 2) * Real.exp (x / 2) := Real.exp_add _ _
        _ = Real.exp (x / 2) ^ 2 := by ring
    have hq : Real.exp (-x) = (E ^ 2)⁻¹ := by
      rw [Real.exp_neg, hsq]
    rw [hq]
    change 1 / (2 * ((E + E⁻¹) / 2) ^ 2) =
      2 * (E ^ 2)⁻¹ * (1 / (1 - (-(E ^ 2)⁻¹)) ^ (1 + 1))
    field_simp [he]
    rw [div_pow]
    field_simp [he]
    ring
  rw [hterms, hval]
  simpa using hsum

open TraceEuclidean.PoitouKernel
open TraceEuclidean.PoitouDegreeEleven

theorem poitouBaseLaplaceIntegral_scale {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      2 * Real.exp (-(a * x)) * (1 - poitouScaledTest y x)) =
      a⁻¹ * poitouBaseLaplaceIntegral (y / a ^ 2) := by
  let g : ℝ → ℝ := fun u =>
    2 * Real.exp (-u) * (1 - poitouScaledTest (y / a ^ 2) u)
  have hsqrt : Real.sqrt (y / a ^ 2) * a = Real.sqrt y := by
    rw [Real.sqrt_div hy.le, Real.sqrt_sq ha.le]
    field_simp [ha.ne']
  have hscale := integral_comp_mul_left_Ioi g 0 ha
  have hleft :
      (∫ x in Set.Ioi (0 : ℝ), g (a * x)) =
      ∫ x in Set.Ioi (0 : ℝ),
        2 * Real.exp (-(a * x)) * (1 - poitouScaledTest y x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only [g, poitouScaledTest]
    rw [show Real.sqrt (y / a ^ 2) * (a * x) =
      (Real.sqrt (y / a ^ 2) * a) * x by ring, hsqrt]
  rw [hleft] at hscale
  simpa only [mul_zero, poitouBaseLaplaceIntegral, smul_eq_mul] using hscale

open TraceEuclidean.PoitouSeriesBounds

theorem poitouOneSubScaled_bounds (y x : ℝ) :
    0 ≤ 1 - poitouScaledTest y x ∧ 1 - poitouScaledTest y x ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (TraceEuclidean.PoitouKernel.poitouTest_le_one _)
  · linarith [poitouScaledTest_nonneg y x]

theorem poitouLaplaceTerm_integrable (y : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ =>
        2 * Real.exp (-(a * x)) * (1 - poitouScaledTest y x))
      (Set.Ioi 0) := by
  have hmajor : IntegrableOn (fun x : ℝ => 2 * Real.exp ((-a) * x))
      (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul 2
  apply hmajor.mono'
  · have hc : Continuous (fun x : ℝ =>
        2 * Real.exp (-(a * x)) * (1 - poitouScaledTest y x)) := by
      exact ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg).const_mul 2).mul
          (continuous_const.sub (poitouScaledTest_continuous y))
    exact hc.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    have he : 0 ≤ Real.exp (-(a * x)) := (Real.exp_pos _).le
    have hb := poitouOneSubScaled_bounds y x
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) he) hb.1)]
    have hexp : Real.exp (-(a * x)) = Real.exp ((-a) * x) := by congr 1 <;> ring
    rw [hexp]
    nlinarith

theorem poitouLClosed_nonneg {y : ℝ} (hy : 0 < y) :
    0 ≤ poitouLClosed y := by
  rw [← TraceEuclidean.PoitouKernel.poitouLClosed_eq_baseLaplaceIntegral hy]
  unfold poitouBaseLaplaceIntegral
  apply integral_nonneg
  intro x
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (poitouOneSubScaled_bounds y x).1

private def poitouOddKernelTerm (k : ℕ) (x : ℝ) : ℝ :=
  (1 - poitouScaledTest poitouY x) *
    (2 * Real.exp (-(((2 * k + 1 : ℕ) : ℝ) * x)))

private def poitouAlternatingKernelTerm (k : ℕ) (x : ℝ) : ℝ :=
  (1 - poitouScaledTest poitouY x) *
    (2 * (-1 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) *
      Real.exp (-(((k + 1 : ℕ) : ℝ) * x)))

private theorem poitouOddKernelTerm_integrable (k : ℕ) :
    IntegrableOn (poitouOddKernelTerm k) (Set.Ioi 0) := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have h := poitouLaplaceTerm_integrable poitouY ha
  apply h.congr
  filter_upwards with x
  dsimp only [poitouOddKernelTerm, a]
  ring

private theorem poitouAlternatingKernelTerm_integrable (k : ℕ) :
    IntegrableOn (poitouAlternatingKernelTerm k) (Set.Ioi 0) := by
  let a : ℝ := ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have h := (poitouLaplaceTerm_integrable poitouY ha).const_mul
    ((-1 : ℝ) ^ k * a)
  apply h.congr
  filter_upwards with x
  dsimp only [poitouAlternatingKernelTerm, a]
  ring

private theorem poitouOddKernelTerm_integral (k : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), poitouOddKernelTerm k x) =
      TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k := by
  let a : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 < poitouY := by norm_num [poitouY]
  calc
    (∫ x in Set.Ioi (0 : ℝ), poitouOddKernelTerm k x) =
        ∫ x in Set.Ioi (0 : ℝ),
          2 * Real.exp (-(a * x)) * (1 - poitouScaledTest poitouY x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [poitouOddKernelTerm, a]
      ring
    _ = a⁻¹ * poitouBaseLaplaceIntegral (poitouY / a ^ 2) :=
      poitouBaseLaplaceIntegral_scale hy ha
    _ = a⁻¹ * poitouLClosed (poitouY / a ^ 2) := by
      rw [poitouLClosed_eq_baseLaplaceIntegral (div_pos hy (sq_pos_of_pos ha))]
    _ = TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k := by
      dsimp only [TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm, a]
      rw [inv_mul_eq_div]

private theorem poitouAlternatingKernelTerm_integral (k : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), poitouAlternatingKernelTerm k x) =
      TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k := by
  let a : ℝ := ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 < poitouY := by norm_num [poitouY]
  calc
    (∫ x in Set.Ioi (0 : ℝ), poitouAlternatingKernelTerm k x) =
        (-1 : ℝ) ^ k * a *
          ∫ x in Set.Ioi (0 : ℝ),
            2 * Real.exp (-(a * x)) * (1 - poitouScaledTest poitouY x) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [poitouAlternatingKernelTerm, a]
      ring
    _ = (-1 : ℝ) ^ k * a *
        (a⁻¹ * poitouBaseLaplaceIntegral (poitouY / a ^ 2)) := by
      rw [poitouBaseLaplaceIntegral_scale hy ha]
    _ = (-1 : ℝ) ^ k * poitouLClosed (poitouY / a ^ 2) := by
      rw [poitouLClosed_eq_baseLaplaceIntegral (div_pos hy (sq_pos_of_pos ha))]
      field_simp [ha.ne']
    _ = TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k := by
      rfl

private theorem poitouOddKernelTerm_integral_norm (k : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), ‖poitouOddKernelTerm k x‖) =
      TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k := by
  rw [← poitouOddKernelTerm_integral k]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change ‖poitouOddKernelTerm k x‖ = poitouOddKernelTerm k x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (poitouOneSubScaled_bounds poitouY x).1 (by positivity)

private theorem poitouAlternatingKernelTerm_integral_norm (k : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), ‖poitouAlternatingKernelTerm k x‖) =
      ‖TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k‖ := by
  let a : ℝ := ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 < poitouY := by norm_num [poitouY]
  have hL : 0 ≤ poitouLClosed (poitouY / a ^ 2) :=
    poitouLClosed_nonneg (div_pos hy (sq_pos_of_pos ha))
  calc
    (∫ x in Set.Ioi (0 : ℝ), ‖poitouAlternatingKernelTerm k x‖) =
        a * ∫ x in Set.Ioi (0 : ℝ),
          2 * Real.exp (-(a * x)) * (1 - poitouScaledTest poitouY x) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change ‖poitouAlternatingKernelTerm k x‖ =
        a * (2 * Real.exp (-(a * x)) * (1 - poitouScaledTest poitouY x))
      rw [Real.norm_eq_abs]
      dsimp only [poitouAlternatingKernelTerm, a]
      have hb := poitouOneSubScaled_bounds poitouY x
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hb.1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg ha.le, abs_of_nonneg (Real.exp_pos _).le]
      ring
    _ = a * (a⁻¹ * poitouBaseLaplaceIntegral (poitouY / a ^ 2)) := by
      rw [poitouBaseLaplaceIntegral_scale hy ha]
    _ = poitouLClosed (poitouY / a ^ 2) := by
      rw [poitouLClosed_eq_baseLaplaceIntegral (div_pos hy (sq_pos_of_pos ha))]
      field_simp [ha.ne']
    _ = ‖TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k‖ := by
      dsimp only [TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm, a]
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg hL, one_mul]

private theorem poitouOddKernel_integral_tsum :
    (∑' k : ℕ, ∫ x in Set.Ioi (0 : ℝ), poitouOddKernelTerm k x) =
      ∫ x in Set.Ioi (0 : ℝ), ∑' k : ℕ, poitouOddKernelTerm k x := by
  apply integral_tsum_of_summable_integral_norm
  · exact poitouOddKernelTerm_integrable
  · have hs := TraceEuclidean.PoitouSeriesBounds.summable_firstPoitouTerm
    apply hs.congr
    intro k
    exact (poitouOddKernelTerm_integral_norm k).symm

private theorem poitouAlternatingKernel_integral_tsum :
    (∑' k : ℕ, ∫ x in Set.Ioi (0 : ℝ), poitouAlternatingKernelTerm k x) =
      ∫ x in Set.Ioi (0 : ℝ), ∑' k : ℕ, poitouAlternatingKernelTerm k x := by
  apply integral_tsum_of_summable_integral_norm
  · exact poitouAlternatingKernelTerm_integrable
  · have hs :=
      TraceEuclidean.PoitouSeriesBounds.summable_alternatingPoitouTerm.norm
    apply hs.congr
    intro k
    exact (poitouAlternatingKernelTerm_integral_norm k).symm

private theorem poitouOddKernel_tsum_pointwise {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, poitouOddKernelTerm k x) =
      (1 - poitouScaledTest poitouY x) / Real.sinh x := by
  have h := (poitouSinhKernel_hasSum hx).mul_left
    (1 - poitouScaledTest poitouY x)
  change (∑' k : ℕ,
    (1 - poitouScaledTest poitouY x) *
      (2 * Real.exp (-(((2 * k + 1 : ℕ) : ℝ) * x)))) = _
  rw [h.tsum_eq]
  ring

private theorem poitouAlternatingKernel_tsum_pointwise {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, poitouAlternatingKernelTerm k x) =
      (1 - poitouScaledTest poitouY x) /
        (2 * Real.cosh (x / 2) ^ 2) := by
  have h := (poitouCoshKernel_hasSum hx).mul_left
    (1 - poitouScaledTest poitouY x)
  change (∑' k : ℕ,
    (1 - poitouScaledTest poitouY x) *
      (2 * (-1 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * x)))) = _
  rw [h.tsum_eq]
  ring

theorem poitouFirstSeries_eq_sinhIntegral :
    (∑' k : ℕ, TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k) =
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - poitouScaledTest poitouY x) / Real.sinh x := by
  calc
    (∑' k : ℕ, TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k) =
        ∑' k : ℕ, ∫ x in Set.Ioi (0 : ℝ), poitouOddKernelTerm k x := by
      apply tsum_congr
      intro k
      exact (poitouOddKernelTerm_integral k).symm
    _ = ∫ x in Set.Ioi (0 : ℝ), ∑' k : ℕ, poitouOddKernelTerm k x :=
      poitouOddKernel_integral_tsum
    _ = ∫ x in Set.Ioi (0 : ℝ),
        (1 - poitouScaledTest poitouY x) / Real.sinh x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact poitouOddKernel_tsum_pointwise hx

theorem poitouAlternatingSeries_eq_coshIntegral :
    (∑' k : ℕ, TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k) =
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - poitouScaledTest poitouY x) /
          (2 * Real.cosh (x / 2) ^ 2) := by
  calc
    (∑' k : ℕ, TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k) =
        ∑' k : ℕ, ∫ x in Set.Ioi (0 : ℝ), poitouAlternatingKernelTerm k x := by
      apply tsum_congr
      intro k
      exact (poitouAlternatingKernelTerm_integral k).symm
    _ = ∫ x in Set.Ioi (0 : ℝ), ∑' k : ℕ, poitouAlternatingKernelTerm k x :=
      poitouAlternatingKernel_integral_tsum
    _ = ∫ x in Set.Ioi (0 : ℝ),
        (1 - poitouScaledTest poitouY x) /
          (2 * Real.cosh (x / 2) ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact poitouAlternatingKernel_tsum_pointwise hx

/-- Poitou's archimedean correction, split into the two absolutely convergent
integrals appearing in the totally real case. -/
def poitouCorrectionIntegral (y : ℝ) : ℝ :=
  (∫ x in Set.Ioi (0 : ℝ),
      (1 - poitouScaledTest y x) / Real.sinh x) +
    ∫ x in Set.Ioi (0 : ℝ),
      (1 - poitouScaledTest y x) /
        (2 * Real.cosh (x / 2) ^ 2)

/-- Poitou's equation (24) at the certified degree-eleven parameter. -/
theorem poitouL1_eq_correctionIntegral :
    poitouL1 poitouY = poitouCorrectionIntegral poitouY := by
  change
    (∑' k : ℕ, TraceEuclidean.PoitouSeriesBounds.firstPoitouTerm k) +
        (∑' k : ℕ,
          TraceEuclidean.PoitouSeriesBounds.alternatingPoitouTerm k) = _
  rw [poitouFirstSeries_eq_sinhIntegral,
    poitouAlternatingSeries_eq_coshIntegral]
  rfl

end

end TraceEuclidean.PoitouKernel
