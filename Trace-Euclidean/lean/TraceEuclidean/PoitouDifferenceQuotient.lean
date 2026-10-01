import TraceEuclidean.PoitouVariation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory Set
open TraceEuclidean.PoitouDegreeEleven

private theorem poitouY_nonneg : 0 ≤ poitouY := by norm_num [poitouY]
private theorem poitouY_le_one : poitouY ≤ 1 := by norm_num [poitouY]

theorem poitouScaledTestDeriv_abs_le_nine_halves_mul_abs (x : ℝ) :
    |poitouScaledTestDeriv poitouY x| ≤ 9 / 2 * |x| := by
  have ha0 : 0 ≤ Real.sqrt poitouY := Real.sqrt_nonneg _
  have haSq : (Real.sqrt poitouY) ^ 2 = poitouY :=
    Real.sq_sqrt poitouY_nonneg
  have htest := poitouTestDeriv_abs_le_nine_halves_mul_abs
    (Real.sqrt poitouY * x)
  rw [poitouScaledTestDeriv, abs_mul, abs_of_nonneg ha0]
  calc
    Real.sqrt poitouY * |poitouTestDeriv (Real.sqrt poitouY * x)| ≤
        Real.sqrt poitouY * (9 / 2 * |Real.sqrt poitouY * x|) :=
      mul_le_mul_of_nonneg_left htest ha0
    _ = 9 / 2 * (Real.sqrt poitouY) ^ 2 * |x| := by
      rw [abs_mul, abs_of_nonneg ha0]
      ring
    _ = 9 / 2 * poitouY * |x| := by rw [haSq]
    _ ≤ 9 / 2 * |x| := by
      have hcoef : (0 : ℝ) ≤ 9 / 2 := by norm_num
      have hycoef : (9 / 2 : ℝ) * poitouY ≤ 9 / 2 :=
        by simpa using mul_le_mul_of_nonneg_left poitouY_le_one hcoef
      exact mul_le_mul_of_nonneg_right hycoef (abs_nonneg x)

theorem poitouScaledTest_one_sub_abs_le (x : ℝ) :
    |1 - poitouScaledTest poitouY x| ≤ 9 / 2 * |x| ^ 2 := by
  let r : ℝ := |x|
  have hr0 : 0 ≤ r := abs_nonneg x
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 r) :
      DifferentiableAt ℝ (poitouScaledTest poitouY) t :=
    (poitouScaledTest_hasDerivAt poitouY t).differentiableAt
  have hbound (t : ℝ) (ht : t ∈ Icc 0 r) :
      ‖deriv (poitouScaledTest poitouY) t‖ ≤ 9 / 2 * r := by
    rw [(poitouScaledTest_hasDerivAt poitouY t).deriv, Real.norm_eq_abs]
    calc
      |poitouScaledTestDeriv poitouY t| ≤ 9 / 2 * |t| :=
        poitouScaledTestDeriv_abs_le_nine_halves_mul_abs t
      _ ≤ 9 / 2 * r := by
        rw [abs_of_nonneg ht.1]
        exact mul_le_mul_of_nonneg_left ht.2 (by norm_num)
  have hmv :
      ‖poitouScaledTest poitouY r - poitouScaledTest poitouY 0‖ ≤
        (9 / 2 * r) * ‖r - 0‖ := by
    exact (convex_Icc (0 : ℝ) r).norm_image_sub_le_of_norm_deriv_le
      hdiff hbound (left_mem_Icc.mpr hr0) (right_mem_Icc.mpr hr0)
  have heven : poitouScaledTest poitouY r = poitouScaledTest poitouY x := by
    dsimp only [r]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, poitouScaledTest_even]
  rw [poitouScaledTest_zero] at hmv
  simp only [Real.norm_eq_abs] at hmv
  simp only [sub_zero] at hmv
  rw [abs_of_nonneg hr0] at hmv
  rw [heven] at hmv
  rw [abs_sub_comm] at hmv
  dsimp only [r] at hmv
  convert hmv using 1 <;> ring

/-- Poitou's second bounded-variation function, with its removable value at
the origin filled by continuity. -/
def poitouDifferenceQuotient (x : ℝ) : ℝ :=
  if x = 0 then 0 else (1 - poitouScaledTest poitouY x) / x

@[simp] theorem poitouDifferenceQuotient_zero :
    poitouDifferenceQuotient 0 = 0 := by
  simp [poitouDifferenceQuotient]

theorem poitouDifferenceQuotient_abs_le (x : ℝ) :
    |poitouDifferenceQuotient x| ≤ 9 / 2 * |x| := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [poitouDifferenceQuotient, if_neg hx, abs_div]
    have hnum := poitouScaledTest_one_sub_abs_le x
    have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
    calc
      |1 - poitouScaledTest poitouY x| / |x| ≤
          (9 / 2 * |x| ^ 2) / |x| :=
        div_le_div_of_nonneg_right hnum (abs_nonneg x)
      _ = 9 / 2 * |x| := by field_simp

theorem poitouDifferenceQuotient_continuousAt_zero :
    ContinuousAt poitouDifferenceQuotient 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let C : ℝ := 9 / 2
  refine ⟨ε / C, by dsimp [C]; positivity, ?_⟩
  intro x hx
  rw [poitouDifferenceQuotient_zero, Real.dist_eq, sub_zero]
  have hq := poitouDifferenceQuotient_abs_le x
  have hx' : |x| < ε / C := by
    simpa [Real.dist_eq, C] using hx
  calc
    |poitouDifferenceQuotient x| ≤ C * |x| := by simpa [C] using hq
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hx' (by norm_num [C])
    _ = ε := by dsimp [C]; field_simp

theorem poitouDifferenceQuotient_continuous :
    Continuous poitouDifferenceQuotient := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using poitouDifferenceQuotient_continuousAt_zero
  · have hreg : ContinuousAt
        (fun z : ℝ ↦ (1 - poitouScaledTest poitouY z) / z) x := by
      exact (continuousAt_const.sub
        (poitouScaledTest_continuous poitouY).continuousAt).div
          continuousAt_id hx
    have heq : poitouDifferenceQuotient =ᶠ[nhds x]
        (fun z : ℝ ↦ (1 - poitouScaledTest poitouY z) / z) := by
      filter_upwards [eventually_ne_nhds hx] with z hz
      simp [poitouDifferenceQuotient, hz]
    exact hreg.congr_of_eventuallyEq heq

def poitouDifferenceQuotientDeriv (x : ℝ) : ℝ :=
  ((-poitouScaledTestDeriv poitouY x) * x -
      (1 - poitouScaledTest poitouY x)) / x ^ 2

theorem poitouDifferenceQuotient_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt poitouDifferenceQuotient
      (poitouDifferenceQuotientDeriv x) x := by
  have hnum := (hasDerivAt_const x 1).sub
    (poitouScaledTest_hasDerivAt poitouY x)
  have hraw := hnum.div (hasDerivAt_id x) hx
  have heq : poitouDifferenceQuotient =ᶠ[nhds x]
      (fun z : ℝ ↦ (1 - poitouScaledTest poitouY z) / z) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    simp [poitouDifferenceQuotient, hz]
  have hraw' := hraw.congr_of_eventuallyEq heq
  unfold poitouDifferenceQuotientDeriv
  convert hraw' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp only [id_eq, Pi.sub_apply]
  all_goals try ring

theorem poitouDifferenceQuotientDeriv_abs_le_nine {x : ℝ} (hx : x ≠ 0) :
    |poitouDifferenceQuotientDeriv x| ≤ 9 := by
  have hd := poitouScaledTestDeriv_abs_le_nine_halves_mul_abs x
  have hn := poitouScaledTest_one_sub_abs_le x
  have hxabs : 0 < |x| := abs_pos.mpr hx
  unfold poitouDifferenceQuotientDeriv
  rw [abs_div, abs_pow]
  calc
    |(-poitouScaledTestDeriv poitouY x) * x -
        (1 - poitouScaledTest poitouY x)| / |x| ^ 2 ≤
        (|poitouScaledTestDeriv poitouY x| * |x| +
          |1 - poitouScaledTest poitouY x|) / |x| ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg |x|)
      simpa only [abs_mul, abs_neg] using
        (abs_sub ((-poitouScaledTestDeriv poitouY x) * x)
          (1 - poitouScaledTest poitouY x))
    _ ≤ ((9 / 2 * |x|) * |x| + 9 / 2 * |x| ^ 2) /
          |x| ^ 2 := by gcongr
    _ = 9 := by field_simp [hxabs.ne'] <;> ring

theorem poitouScaledTestDeriv_abs_le_far {x : ℝ} (hx : 2 ≤ |x|) :
    |poitouScaledTestDeriv poitouY x| ≤ 2016 / |x| ^ 4 := by
  let a : ℝ := Real.sqrt poitouY
  have ha : (1 / 2 : ℝ) ≤ a := by
    dsimp only [a]
    linarith [sqrt_y_bounds.1]
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hax : 1 ≤ |a * x| := by
    rw [abs_mul, abs_of_pos ha0]
    nlinarith
  have ht := poitouTestDeriv_abs_le_twoFiftyTwo_div_fourth hax
  have hcub : (1 / 8 : ℝ) ≤ a ^ 3 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ha 3
    norm_num at hpow ⊢
    exact hpow
  rw [poitouScaledTestDeriv, abs_mul, abs_of_pos ha0]
  calc
    a * |poitouTestDeriv (a * x)| ≤ a * (252 / |a * x| ^ 4) :=
      mul_le_mul_of_nonneg_left ht ha0.le
    _ = 252 / (a ^ 3 * |x| ^ 4) := by
      rw [abs_mul, abs_of_pos ha0]
      field_simp [ha0.ne']
    _ ≤ 2016 / |x| ^ 4 := by
      have hx0 : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
      apply (div_le_iff₀ (mul_pos (pow_pos ha0 3) (pow_pos hx0 4))).2
      field_simp [hx0.ne']
      nlinarith

theorem poitouDifferenceQuotientDeriv_abs_le_far {x : ℝ}
    (hx : 2 ≤ |x|) :
    |poitouDifferenceQuotientDeriv x| ≤ 2020 / |x| ^ 2 := by
  have hx0 : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
  have hd := poitouScaledTestDeriv_abs_le_far hx
  have htest0 := poitouScaledTest_nonneg poitouY x
  have htest := poitouScaledTest_le_nine_fourths poitouY x
  have hnum : |1 - poitouScaledTest poitouY x| ≤ 13 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  unfold poitouDifferenceQuotientDeriv
  rw [abs_div, abs_pow]
  calc
    |(-poitouScaledTestDeriv poitouY x) * x -
        (1 - poitouScaledTest poitouY x)| / |x| ^ 2 ≤
        (|poitouScaledTestDeriv poitouY x| * |x| +
          |1 - poitouScaledTest poitouY x|) / |x| ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg |x|)
      simpa only [abs_mul, abs_neg] using
        (abs_sub ((-poitouScaledTestDeriv poitouY x) * x)
          (1 - poitouScaledTest poitouY x))
    _ ≤ ((2016 / |x| ^ 4) * |x| + 13 / 4) / |x| ^ 2 := by
      gcongr
    _ ≤ 2020 / |x| ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg |x|)
      have hpow : 1 ≤ |x| ^ 3 := by nlinarith [sq_nonneg |x|]
      have hterm : (2016 / |x| ^ 4) * |x| ≤ 2016 := by
        calc
          (2016 / |x| ^ 4) * |x| = 2016 / |x| ^ 3 := by
            field_simp [hx0.ne']
          _ ≤ 2016 := div_le_self (by norm_num) hpow
      linarith

theorem poitouDifferenceQuotientDeriv_majorant {x : ℝ} (hx : x ≠ 0) :
    |poitouDifferenceQuotientDeriv x| ≤ 10000 / (1 + x ^ 2) := by
  by_cases hnear : |x| < 2
  · have hd := poitouDifferenceQuotientDeriv_abs_le_nine hx
    have hden : 1 + x ^ 2 < 5 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hden0 : 0 < 1 + x ^ 2 := by positivity
    apply hd.trans
    rw [le_div_iff₀ hden0]
    nlinarith
  · have hfar : 2 ≤ |x| := le_of_not_gt hnear
    have hd := poitouDifferenceQuotientDeriv_abs_le_far hfar
    have hxSq : (4 : ℝ) ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hxSqPos : 0 < x ^ 2 := lt_of_lt_of_le (by norm_num) hxSq
    have hden0 : 0 < 1 + x ^ 2 := by positivity
    apply hd.trans
    rw [sq_abs]
    rw [div_le_div_iff₀ hxSqPos hden0]
    nlinarith

theorem poitouDifferenceQuotient_boundedVariation :
    BoundedVariationOn poitouDifferenceQuotient Set.univ := by
  let B : ℝ → ℝ := fun x ↦ 10000 / (1 + x ^ 2)
  have hBi : Integrable B volume := by
    dsimp only [B]
    simpa only [div_eq_mul_inv] using
      integrable_inv_one_add_sq.const_mul (10000 : ℝ)
  have hB0 (x : ℝ) : 0 ≤ B x := by
    dsimp only [B]
    positivity
  have hleft : BoundedVariationOn poitouDifferenceQuotient (Iic 0) := by
    apply boundedVariationOn_of_integrable_deriv_bound
      (f := poitouDifferenceQuotient) (B := B)
    · exact poitouDifferenceQuotient_continuous
    · intro a ha b hb x hx
      exact (poitouDifferenceQuotient_hasDerivAt (by
        have hb0 : b ≤ 0 := hb
        exact ne_of_lt (hx.2.trans_le hb0))).differentiableAt.differentiableWithinAt
    · intro a ha b hb x hx
      exact hx.2.le.trans hb
    · intro a ha b hb x hx hx0
      subst x
      exact (not_lt_of_ge hb hx.2).elim
    · exact hB0
    · intro x hx hx0
      rw [(poitouDifferenceQuotient_hasDerivAt hx0).deriv, Real.norm_eq_abs]
      exact poitouDifferenceQuotientDeriv_majorant hx0
    · exact hBi
  have hright : BoundedVariationOn poitouDifferenceQuotient (Ici 0) := by
    apply boundedVariationOn_of_integrable_deriv_bound
      (f := poitouDifferenceQuotient) (B := B)
    · exact poitouDifferenceQuotient_continuous
    · intro a ha b hb x hx
      exact (poitouDifferenceQuotient_hasDerivAt (by
        have ha0 : 0 ≤ a := ha
        exact ne_of_gt (ha0.trans_lt hx.1))).differentiableAt.differentiableWithinAt
    · intro a ha b hb x hx
      exact ha.trans hx.1.le
    · intro a ha b hb x hx hx0
      subst x
      exact (not_lt_of_ge ha hx.1).elim
    · exact hB0
    · intro x hx hx0
      rw [(poitouDifferenceQuotient_hasDerivAt hx0).deriv, Real.norm_eq_abs]
      exact poitouDifferenceQuotientDeriv_majorant hx0
    · exact hBi
  unfold BoundedVariationOn at hleft hright ⊢
  rw [← Set.Iic_union_Ici (a := (0 : ℝ)),
    eVariationOn.union poitouDifferenceQuotient
      (show IsGreatest (Iic 0) 0 from ⟨by simp, fun _ h ↦ h⟩)
      (show IsLeast (Ici 0) 0 from ⟨by simp, fun _ h ↦ h⟩)]
  exact ENNReal.add_ne_top.mpr ⟨hleft, hright⟩

end

end TraceEuclidean.PoitouKernel
