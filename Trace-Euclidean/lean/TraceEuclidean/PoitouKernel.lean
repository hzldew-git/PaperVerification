import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Poitou--Tartar test function

Poitou's unconditional discriminant inequality uses the square of the
Fourier transform of the normalized bump `3/4 * (1 - t^2)` on `[-1,1]`.
This module defines that function by its compact interval integral, proves
the trigonometric closed form used in the source, and establishes the basic
positivity and integrability properties needed by the explicit formula.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory intervalIntegral

/-- The normalized polynomial bump before applying the support cutoff. -/
def poitouBumpCore (t : ℝ) : ℝ :=
  (3 / 4 : ℝ) * (1 - t ^ 2)

/-- The real Fourier amplitude in Poitou's angular-frequency normalization. -/
def poitouAmplitude (x : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, poitouBumpCore t * Real.cos (x * t)

/-- Poitou's nonnegative test function. -/
def poitouTest (x : ℝ) : ℝ := poitouAmplitude x ^ 2

private def poitouAmplitudePrimitive (x t : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    ((1 - t ^ 2) * Real.sin (x * t) / x -
      2 * t * Real.cos (x * t) / x ^ 2 +
      2 * Real.sin (x * t) / x ^ 3)

private theorem poitouAmplitudePrimitive_hasDerivAt
    {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (poitouAmplitudePrimitive x)
      (poitouBumpCore t * Real.cos (x * t)) t := by
  have hsin : HasDerivAt (fun u : ℝ ↦ Real.sin (x * u))
      (Real.cos (x * t) * x) t := by
    have harg : HasDerivAt (fun u : ℝ ↦ x * u) x t :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul x
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (x * t)).comp t harg
  have hcos : HasDerivAt (fun u : ℝ ↦ Real.cos (x * u))
      (-Real.sin (x * t) * x) t := by
    have harg : HasDerivAt (fun u : ℝ ↦ x * u) x t :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul x
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (x * t)).comp t harg
  have hpoly : HasDerivAt (fun u : ℝ ↦ 1 - u ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2) using 1
    all_goals first
      | (with_reducible_and_instances rfl)
      | (funext u; rfl)
      | (simp only [id_eq]; ring)
  have hfirst : HasDerivAt
      (fun u : ℝ ↦ (1 - u ^ 2) * Real.sin (x * u) / x)
      (((-2 * t) * Real.sin (x * t) +
        (1 - t ^ 2) * (Real.cos (x * t) * x)) / x) t :=
    (hpoly.mul hsin).div_const x
  have hsecond : HasDerivAt
      (fun u : ℝ ↦ 2 * u * Real.cos (x * u) / x ^ 2)
      ((2 * Real.cos (x * t) +
        2 * t * (-Real.sin (x * t) * x)) / x ^ 2) t := by
    have hlin : HasDerivAt (fun u : ℝ ↦ 2 * u) 2 t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
    convert (hlin.mul hcos).div_const (x ^ 2) using 1
    all_goals first | (with_reducible_and_instances rfl) | (funext u; rfl) | ring
  have hthird : HasDerivAt
      (fun u : ℝ ↦ 2 * Real.sin (x * u) / x ^ 3)
      (2 * (Real.cos (x * t) * x) / x ^ 3) t :=
    (hsin.const_mul 2).div_const (x ^ 3)
  unfold poitouAmplitudePrimitive
  convert ((hfirst.sub hsecond).add hthird).const_mul (3 / 4 : ℝ) using 1
  all_goals first
    | (with_reducible_and_instances rfl)
    | (funext u; rfl)
    | (unfold poitouBumpCore; field_simp [hx]; ring)

/-- Closed trigonometric expression for the source amplitude away from the
removable origin. -/
theorem poitouAmplitude_eq {x : ℝ} (hx : x ≠ 0) :
    poitouAmplitude x =
      3 * (Real.sin x - x * Real.cos x) / x ^ 3 := by
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ poitouBumpCore t * Real.cos (x * t))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold poitouBumpCore
    fun_prop
  rw [poitouAmplitude,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ poitouAmplitudePrimitive_hasDerivAt hx t) hint]
  unfold poitouAmplitudePrimitive
  simp only [one_pow, mul_one, neg_one_sq, sub_self, zero_mul, zero_div,
    mul_neg, mul_neg_one, Real.sin_neg, Real.cos_neg]
  field_simp [hx]
  ring

/-- The normalization makes the test function equal to one at the origin. -/
@[simp] theorem poitouAmplitude_zero : poitouAmplitude 0 = 1 := by
  have hint : IntervalIntegrable poitouBumpCore volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold poitouBumpCore
    fun_prop
  have hder (t : ℝ) :
      HasDerivAt (fun u : ℝ ↦ (3 / 4 : ℝ) * (u - u ^ 3 / 3))
        (poitouBumpCore t) t := by
    unfold poitouBumpCore
    convert (((hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 3).div_const 3)).const_mul (3 / 4 : ℝ)) using 1
    all_goals (try with_reducible_and_instances rfl)
    all_goals (try funext u)
    all_goals (try simp only [id_eq])
    all_goals norm_num <;> ring
  rw [poitouAmplitude]
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hder t) hint]
  norm_num

@[simp] theorem poitouTest_zero : poitouTest 0 = 1 := by
  simp [poitouTest]

/-- The amplitude is even. -/
theorem poitouAmplitude_even (x : ℝ) :
    poitouAmplitude (-x) = poitouAmplitude x := by
  unfold poitouAmplitude
  apply intervalIntegral.integral_congr
  intro t _
  change poitouBumpCore t * Real.cos (-x * t) =
    poitouBumpCore t * Real.cos (x * t)
  rw [show -x * t = -(x * t) by ring, Real.cos_neg]

/-- Poitou's test function is even. -/
theorem poitouTest_even (x : ℝ) : poitouTest (-x) = poitouTest x := by
  rw [poitouTest, poitouTest, poitouAmplitude_even]

/-- Poitou's test function is pointwise nonnegative. -/
theorem poitouTest_nonneg (x : ℝ) : 0 ≤ poitouTest x := by
  exact sq_nonneg _

/-- The source's displayed square formula, including its normalization at
the removable origin. -/
theorem poitouTest_eq {x : ℝ} (hx : x ≠ 0) :
    poitouTest x =
      (3 * (Real.sin x - x * Real.cos x) / x ^ 3) ^ 2 := by
  rw [poitouTest, poitouAmplitude_eq hx]

/-- The amplitude depends continuously on its angular frequency. -/
theorem poitouAmplitude_continuous : Continuous poitouAmplitude := by
  unfold poitouAmplitude
  have hwhole : Continuous (Function.uncurry fun x t : ℝ ↦
      poitouBumpCore t * Real.cos (x * t)) := by
    unfold poitouBumpCore
    fun_prop
  exact continuous_parametric_intervalIntegral_of_continuous'
    hwhole (-1) 1

/-- Poitou's test function is continuous. -/
theorem poitouTest_continuous : Continuous poitouTest := by
  unfold poitouTest
  exact poitouAmplitude_continuous.pow 2

theorem poitouAmplitude_abs_le_three_halves (x : ℝ) :
    |poitouAmplitude x| ≤ 3 / 2 := by
  rw [poitouAmplitude]
  calc
    |∫ t in (-1 : ℝ)..1,
        poitouBumpCore t * Real.cos (x * t)| ≤
        (3 / 4 : ℝ) * |(1 : ℝ) - (-1)| := by
      change ‖∫ t in (-1 : ℝ)..1,
        poitouBumpCore t * Real.cos (x * t)‖ ≤ _
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      rw [Real.norm_eq_abs, abs_mul]
      have hbump : |poitouBumpCore t| ≤ 3 / 4 := by
        have htAbs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        have htSq : t ^ 2 ≤ 1 := by
          have hp := pow_le_pow_left₀ (abs_nonneg t) htAbs 2
          simpa only [sq_abs, one_pow] using hp
        have hnonneg : 0 ≤ poitouBumpCore t := by
          unfold poitouBumpCore
          positivity
        rw [abs_of_nonneg hnonneg]
        unfold poitouBumpCore
        nlinarith
      calc
        |poitouBumpCore t| * |Real.cos (x * t)| ≤
            (3 / 4 : ℝ) * 1 :=
          mul_le_mul hbump (Real.abs_cos_le_one (x * t))
            (abs_nonneg _) (by norm_num)
        _ = 3 / 4 := by norm_num
    _ = 3 / 2 := by norm_num

theorem poitouAmplitude_abs_le_six_div_sq {x : ℝ}
    (hx : 1 ≤ |x|) :
    |poitouAmplitude x| ≤ 6 / |x| ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hnum : |Real.sin x - x * Real.cos x| ≤ 1 + |x| := by
    calc
      |Real.sin x - x * Real.cos x| ≤
          |Real.sin x| + |x * Real.cos x| := abs_sub _ _
      _ = |Real.sin x| + |x| * |Real.cos x| := by rw [abs_mul]
      _ ≤ 1 + |x| * 1 := add_le_add (Real.abs_sin_le_one x)
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg x))
      _ = 1 + |x| := by ring
  have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hlin : 1 + |x| ≤ 2 * |x| := by linarith
  rw [poitouAmplitude_eq hx0]
  calc
    |3 * (Real.sin x - x * Real.cos x) / x ^ 3| =
        3 * |Real.sin x - x * Real.cos x| / |x| ^ 3 := by
      rw [abs_div, abs_mul, abs_pow]
      norm_num
    _ ≤
        3 * (2 * |x|) / |x| ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hnum.trans hlin) (by norm_num))
        (by positivity)
    _ = 6 / |x| ^ 2 := by field_simp [ne_of_gt hxpos]; ring

/-- The fourth-power decay needed for integrability of Poitou's test
function. -/
theorem poitouTest_le_majorant (x : ℝ) :
    poitouTest x ≤ 576 / (1 + |x|) ^ 4 := by
  by_cases hx : |x| ≤ 1
  · have ha := poitouAmplitude_abs_le_three_halves x
    have htest : poitouTest x ≤ 9 / 4 := by
      rw [poitouTest, ← sq_abs]
      have hsquare := pow_le_pow_left₀
        (abs_nonneg (poitouAmplitude x)) ha 2
      norm_num at hsquare ⊢
      exact hsquare
    have htwo : 1 + |x| ≤ 2 := by linarith
    have hden : (1 + |x|) ^ 4 ≤ 16 := by
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |x|) htwo 4
      norm_num at hpow ⊢
      exact hpow
    have hdenpos : 0 < (1 + |x|) ^ 4 := by positivity
    have hmajor : (9 / 4 : ℝ) ≤ 576 / (1 + |x|) ^ 4 := by
      rw [le_div_iff₀ hdenpos]
      nlinarith
    exact htest.trans hmajor
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    have ha := poitouAmplitude_abs_le_six_div_sq hx'
    have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx'
    have htest : poitouTest x ≤ 36 / |x| ^ 4 := by
      rw [poitouTest, ← sq_abs]
      have hsquare := pow_le_pow_left₀
        (abs_nonneg (poitouAmplitude x)) ha 2
      calc
        |poitouAmplitude x| ^ 2 ≤ (6 / |x| ^ 2) ^ 2 := hsquare
        _ = 36 / |x| ^ 4 := by field_simp; ring
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hpow : (1 + |x|) ^ 4 ≤ 16 * |x| ^ 4 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |x|)
        hsum 4]
    have hmajor : 36 / |x| ^ 4 ≤ 576 / (1 + |x|) ^ 4 := by
      rw [div_le_div_iff₀ (pow_pos hxpos 4) (by positivity : 0 < (1 + |x|) ^ 4)]
      nlinarith
    exact htest.trans hmajor

/-- Poitou's test function is Lebesgue integrable. -/
theorem poitouTest_integrable : Integrable poitouTest volume := by
  have hbase : Integrable
      (fun x : ℝ ↦ 576 * (1 + ‖x‖) ^ (-(4 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (4 : ℝ)) (by norm_num)).const_mul 576
  have hmajor : (fun x : ℝ ↦ 576 / (1 + |x|) ^ 4) =
      (fun x : ℝ ↦ 576 * (1 + ‖x‖) ^ (-(4 : ℝ))) := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
    norm_num [div_eq_mul_inv, Real.rpow_natCast]
  rw [← hmajor] at hbase
  apply hbase.mono' poitouTest_continuous.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (poitouTest_nonneg x)]
  exact poitouTest_le_majorant x

end

end TraceEuclidean.PoitouKernel
