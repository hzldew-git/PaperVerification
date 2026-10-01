import TraceEuclidean.PoitouKernel
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

def poitouAmplitudeDeriv (x : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    poitouBumpCore t * (-Real.sin (x * t) * t)

theorem poitouAmplitude_hasDerivAt (x : ℝ) :
    HasDerivAt poitouAmplitude (poitouAmplitudeDeriv x) x := by
  let F : ℝ → ℝ → ℝ := fun u t ↦
    poitouBumpCore t * Real.cos (u * t)
  let F' : ℝ → ℝ → ℝ := fun u t ↦
    poitouBumpCore t * (-Real.sin (u * t) * t)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (F := F) (F' := F')
    (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (x₀ := x) (s := Set.univ) (bound := fun _ : ℝ ↦ (3 / 4 : ℝ))
    (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    (Filter.Eventually.of_forall fun u ↦ by
      apply Continuous.aestronglyMeasurable
      simp only [F]
      unfold poitouBumpCore
      fun_prop)
    (by
      apply Continuous.intervalIntegrable
      simp only [F]
      unfold poitouBumpCore
      fun_prop)
    (by
      apply Continuous.aestronglyMeasurable
      simp only [F']
      unfold poitouBumpCore
      fun_prop)
    (Filter.Eventually.of_forall fun t ht u _ ↦ by
      simp only [F']
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_neg]
      have htAbs : |t| ≤ 1 := by
        rw [uIoc_of_le (by norm_num)] at ht
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have htSq : t ^ 2 ≤ 1 := by
        have hp := pow_le_pow_left₀ (abs_nonneg t) htAbs 2
        simpa only [sq_abs, one_pow] using hp
      have hbump : |poitouBumpCore t| ≤ 3 / 4 := by
        have hcoreNonneg : 0 ≤ poitouBumpCore t := by
          unfold poitouBumpCore
          positivity
        rw [abs_of_nonneg hcoreNonneg]
        unfold poitouBumpCore
        nlinarith [sq_nonneg t]
      calc
        |poitouBumpCore t| * (|Real.sin (u * t)| * |t|) ≤
            (3 / 4 : ℝ) * (1 * 1) := by
          gcongr
          · exact Real.abs_sin_le_one _
        _ = 3 / 4 := by norm_num)
    (by
      apply Continuous.intervalIntegrable
      fun_prop)
    (Filter.Eventually.of_forall fun t _ u _ ↦ by
      simp only [F, F']
      have harg : HasDerivAt (fun z : ℝ ↦ z * t) t u := by
        simpa only [id_eq, one_mul] using (hasDerivAt_id u).mul_const t
      convert ((Real.hasDerivAt_cos (u * t)).comp u harg).const_mul
        (poitouBumpCore t) using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [Function.comp_def])
  change HasDerivAt
    (fun u : ℝ ↦ ∫ t in (-1 : ℝ)..1,
      poitouBumpCore t * Real.cos (u * t))
    (∫ t in (-1 : ℝ)..1,
      poitouBumpCore t * (-Real.sin (x * t) * t)) x
  exact h.2

theorem poitouAmplitude_differentiable : Differentiable ℝ poitouAmplitude :=
  fun x ↦ (poitouAmplitude_hasDerivAt x).differentiableAt

theorem poitouAmplitudeDeriv_abs_le_three_halves (x : ℝ) :
    |poitouAmplitudeDeriv x| ≤ 3 / 2 := by
  rw [poitouAmplitudeDeriv]
  change ‖∫ t in (-1 : ℝ)..1,
      poitouBumpCore t * (-Real.sin (x * t) * t)‖ ≤ _
  calc
    ‖∫ t in (-1 : ℝ)..1,
        poitouBumpCore t * (-Real.sin (x * t) * t)‖ ≤
        (3 / 4 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_neg]
      have htAbs : |t| ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num)] at ht
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have htSq : t ^ 2 ≤ 1 := by
        have hp := pow_le_pow_left₀ (abs_nonneg t) htAbs 2
        simpa only [sq_abs, one_pow] using hp
      have hcoreNonneg : 0 ≤ poitouBumpCore t := by
        unfold poitouBumpCore
        positivity
      have hbump : |poitouBumpCore t| ≤ 3 / 4 := by
        rw [abs_of_nonneg hcoreNonneg]
        unfold poitouBumpCore
        nlinarith [sq_nonneg t]
      calc
        |poitouBumpCore t| * (|Real.sin (x * t)| * |t|) ≤
            (3 / 4 : ℝ) * (1 * 1) := by
          gcongr
          · exact Real.abs_sin_le_one _
        _ = 3 / 4 := by norm_num
    _ = 3 / 2 := by norm_num

theorem poitouAmplitudeDeriv_abs_le_three_halves_mul_abs (x : ℝ) :
    |poitouAmplitudeDeriv x| ≤ 3 / 2 * |x| := by
  rw [poitouAmplitudeDeriv]
  change ‖∫ t in (-1 : ℝ)..1,
      poitouBumpCore t * (-Real.sin (x * t) * t)‖ ≤ _
  calc
    ‖∫ t in (-1 : ℝ)..1,
        poitouBumpCore t * (-Real.sin (x * t) * t)‖ ≤
        (3 / 4 * |x| : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_neg]
      have htAbs : |t| ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num)] at ht
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have htSq : t ^ 2 ≤ 1 := by
        have hp := pow_le_pow_left₀ (abs_nonneg t) htAbs 2
        simpa only [sq_abs, one_pow] using hp
      have hbump : |poitouBumpCore t| ≤ 3 / 4 := by
        have hcoreNonneg : 0 ≤ poitouBumpCore t := by
          unfold poitouBumpCore
          positivity
        rw [abs_of_nonneg hcoreNonneg]
        unfold poitouBumpCore
        nlinarith [sq_nonneg t]
      calc
        |poitouBumpCore t| * (|Real.sin (x * t)| * |t|) ≤
            (3 / 4 : ℝ) * (|x * t| * |t|) := by
          have hsin : |Real.sin (x * t)| * |t| ≤ |x * t| * |t| :=
            mul_le_mul_of_nonneg_right Real.abs_sin_le_abs (abs_nonneg t)
          exact mul_le_mul hbump hsin
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
        _ = (3 / 4 : ℝ) * |x| * |t| ^ 2 := by
          rw [abs_mul]
          ring
        _ ≤ (3 / 4 : ℝ) * |x| * 1 := by
          gcongr
          simpa only [sq_abs] using htSq
        _ = 3 / 4 * |x| := by ring
    _ = 3 / 2 * |x| := by ring

theorem poitouAmplitudeDeriv_eq {x : ℝ} (hx : x ≠ 0) :
    poitouAmplitudeDeriv x =
      3 * ((x ^ 2 - 3) * Real.sin x + 3 * x * Real.cos x) / x ^ 4 := by
  let g : ℝ → ℝ := fun z ↦
    (Real.sin z - z * Real.cos z) / z ^ 3 * 3
  have hnum : HasDerivAt (fun z : ℝ ↦ Real.sin z - z * Real.cos z)
      (x * Real.sin x) x := by
    convert (Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try { funext z; rfl }
    all_goals simp only [id_eq]
    all_goals try ring
  have hden : HasDerivAt (fun z : ℝ ↦ z ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try { funext z; rfl }
    all_goals try norm_num
  have hg : HasDerivAt g
      (3 * ((x ^ 2 - 3) * Real.sin x + 3 * x * Real.cos x) / x ^ 4) x := by
    have hraw := (hnum.div hden (pow_ne_zero 3 hx)).const_mul 3
    dsimp only [g]
    convert hraw using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try { funext z; simp only [Pi.div_apply]; ring }
    field_simp [hx]
    ring
  have heq : poitouAmplitude =ᶠ[𝓝 x] g := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    rw [poitouAmplitude_eq hz]
    dsimp only [g]
    ring
  have hg' := hg.congr_of_eventuallyEq heq
  exact (poitouAmplitude_hasDerivAt x).unique hg'

theorem poitouAmplitudeDeriv_abs_le_twentyOne_div_sq {x : ℝ}
    (hx : 1 ≤ |x|) :
    |poitouAmplitudeDeriv x| ≤ 21 / |x| ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hnum :
      |(x ^ 2 - 3) * Real.sin x + 3 * x * Real.cos x| ≤
        7 * |x| ^ 2 := by
    calc
      |(x ^ 2 - 3) * Real.sin x + 3 * x * Real.cos x| ≤
          |(x ^ 2 - 3) * Real.sin x| +
            |3 * x * Real.cos x| := abs_add_le _ _
      _ =
          |x ^ 2 - 3| * |Real.sin x| +
            3 * |x| * |Real.cos x| := by
        rw [abs_mul, abs_mul, abs_mul]
        norm_num
      _ ≤ |x ^ 2 - 3| * 1 + 3 * |x| * 1 := by
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
      _ ≤ (x ^ 2 + 3) + 3 * |x| := by
        have habs : |x ^ 2 - 3| ≤ x ^ 2 + 3 := by
          calc
            |x ^ 2 - 3| ≤ |x ^ 2| + |(3 : ℝ)| := abs_sub _ _
            _ = x ^ 2 + 3 := by simp
        linarith
      _ ≤ 7 * |x| ^ 2 := by
        have hsq : (1 : ℝ) ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
        have hlin : |x| ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
        rw [sq_abs] at hsq hlin ⊢
        nlinarith
  rw [poitouAmplitudeDeriv_eq hx0, abs_div, abs_mul, abs_pow]
  norm_num
  calc
    3 * |(x ^ 2 - 3) * Real.sin x + 3 * x * Real.cos x| / |x| ^ 4 ≤
        3 * (7 * |x| ^ 2) / |x| ^ 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (by norm_num)) (by positivity)
    _ = 21 / x ^ 2 := by
      field_simp [hx0, ne_of_gt hxpos]
      rw [sq_abs]
      ring

def poitouTestDeriv (x : ℝ) : ℝ :=
  2 * poitouAmplitude x * poitouAmplitudeDeriv x

theorem poitouTest_hasDerivAt (x : ℝ) :
    HasDerivAt poitouTest (poitouTestDeriv x) x := by
  unfold poitouTest poitouTestDeriv
  have h := (poitouAmplitude_hasDerivAt x).mul
    (poitouAmplitude_hasDerivAt x)
  have heq : (fun z : ℝ ↦ poitouAmplitude z ^ 2) =ᶠ[𝓝 x]
      (poitouAmplitude * poitouAmplitude) :=
    Filter.Eventually.of_forall fun z ↦ by simp [pow_two]
  have h' := h.congr_of_eventuallyEq heq
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals ring

theorem poitouTest_differentiable : Differentiable ℝ poitouTest :=
  fun x ↦ (poitouTest_hasDerivAt x).differentiableAt

theorem poitouTestDeriv_abs_le_nine_halves (x : ℝ) :
    |poitouTestDeriv x| ≤ 9 / 2 := by
  rw [poitouTestDeriv, abs_mul, abs_mul]
  have ha := poitouAmplitude_abs_le_three_halves x
  have had := poitouAmplitudeDeriv_abs_le_three_halves x
  norm_num at ha had ⊢
  nlinarith [abs_nonneg (poitouAmplitude x), abs_nonneg (poitouAmplitudeDeriv x)]

theorem poitouTestDeriv_abs_le_nine_halves_mul_abs (x : ℝ) :
    |poitouTestDeriv x| ≤ 9 / 2 * |x| := by
  rw [poitouTestDeriv, abs_mul, abs_mul]
  have ha := poitouAmplitude_abs_le_three_halves x
  have had := poitouAmplitudeDeriv_abs_le_three_halves_mul_abs x
  nlinarith [abs_nonneg (poitouAmplitude x), abs_nonneg (poitouAmplitudeDeriv x),
    abs_nonneg x]

theorem poitouTestDeriv_abs_le_twoFiftyTwo_div_fourth {x : ℝ}
    (hx : 1 ≤ |x|) :
    |poitouTestDeriv x| ≤ 252 / |x| ^ 4 := by
  rw [poitouTestDeriv, abs_mul, abs_mul]
  norm_num
  have ha := poitouAmplitude_abs_le_six_div_sq hx
  have had := poitouAmplitudeDeriv_abs_le_twentyOne_div_sq hx
  have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  calc
    2 * |poitouAmplitude x| * |poitouAmplitudeDeriv x| ≤
        2 * (6 / |x| ^ 2) * (21 / |x| ^ 2) := by
      gcongr
    _ = 252 / |x| ^ 4 := by
      field_simp [ne_of_gt hxpos]
      ring

end

end TraceEuclidean.PoitouKernel
