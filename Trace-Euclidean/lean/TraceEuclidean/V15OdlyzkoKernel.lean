import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Odlyzko's unconditional test kernel at `b = 4`

This file formalizes the elementary kernel printed in Odlyzko's November 29,
1976 description of the discriminant-bound tables.  The source defines an even
function `H`, supported on `[-2, 2]`, and uses

`F(x) = H(x / b) / cosh(x / 2)`

in the unconditional explicit formula.  The paper v15 uses the row `b = 4`.
The analytic explicit formula and the archimedean integral estimates are not
claimed here.
-/

namespace TraceEuclidean

noncomputable section

/-- The formula for Odlyzko's unconditional auxiliary function on `[0, 2]`. -/
def v15OdlyzkoHCore (t : ℝ) : ℝ :=
  (2 - t) * (1 + Real.cos (Real.pi * t) / 2) / 3 +
    Real.sin (Real.pi * t) / (2 * Real.pi)

/-- Odlyzko's even compactly supported auxiliary function `H`. -/
def v15OdlyzkoH (x : ℝ) : ℝ :=
  if |x| ≤ 2 then v15OdlyzkoHCore |x| else 0

/-- The unconditional Odlyzko kernel for the Table 4 row `b = 4`. -/
def v15OdlyzkoF4 (x : ℝ) : ℝ :=
  v15OdlyzkoH (x / 4) / Real.cosh (x / 2)

@[simp] theorem v15OdlyzkoHCore_two : v15OdlyzkoHCore 2 = 0 := by
  rw [v15OdlyzkoHCore, show Real.pi * 2 = 2 * Real.pi by ring,
    Real.cos_two_pi, Real.sin_two_pi]
  norm_num

private def v15OdlyzkoR (x : ℝ) : ℝ :=
  2 * Real.sin (x / 2) - x * Real.cos (x / 2)

private def v15OdlyzkoQ (x : ℝ) : ℝ :=
  x * (2 + Real.cos x) - 3 * Real.sin x

private theorem v15OdlyzkoR_hasDerivAt (x : ℝ) :
    HasDerivAt v15OdlyzkoR (x / 2 * Real.sin (x / 2)) x := by
  unfold v15OdlyzkoR
  convert
    (((Real.hasDerivAt_sin (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).const_mul 2).sub
      ((hasDerivAt_id x).mul
        ((Real.hasDerivAt_cos (x / 2)).comp x ((hasDerivAt_id x).div_const 2))) using 1
  all_goals first | rfl | (simp only [Function.comp_apply, id_eq]; ring_nf)

private theorem v15OdlyzkoR_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ v15OdlyzkoR x := by
  have hmono : MonotoneOn v15OdlyzkoR (Set.Icc 0 Real.pi) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi) (by
      unfold v15OdlyzkoR
      fun_prop)
      (fun y _ ↦ (v15OdlyzkoR_hasDerivAt y).hasDerivWithinAt) (by
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) Real.pi := interior_subset hy
        exact mul_nonneg (div_nonneg hy'.1 (by norm_num))
          (Real.sin_nonneg_of_nonneg_of_le_pi
            (div_nonneg hy'.1 (by norm_num)) (by nlinarith [hy'.2, Real.pi_pos])))
  have h := hmono (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx₀, hxπ⟩) hx₀
  simpa [v15OdlyzkoR] using h

private theorem v15OdlyzkoQ_hasDerivAt (x : ℝ) :
    HasDerivAt v15OdlyzkoQ (2 - 2 * Real.cos x - x * Real.sin x) x := by
  unfold v15OdlyzkoQ
  convert
    ((hasDerivAt_id x).mul
      ((hasDerivAt_const x 2).add (Real.hasDerivAt_cos x))).sub
      ((Real.hasDerivAt_sin x).const_mul 3) using 1
  all_goals first | rfl | (simp only [Pi.add_apply, id_eq]; ring_nf)

private theorem v15OdlyzkoQ_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ v15OdlyzkoQ x := by
  have hmono : MonotoneOn v15OdlyzkoQ (Set.Icc 0 Real.pi) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi) (by
      unfold v15OdlyzkoQ
      fun_prop)
      (fun y _ ↦ (v15OdlyzkoQ_hasDerivAt y).hasDerivWithinAt) (by
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) Real.pi := interior_subset hy
        have hr : 0 ≤ v15OdlyzkoR y := v15OdlyzkoR_nonneg hy'.1 hy'.2
        have hs : 0 ≤ Real.sin (y / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg hy'.1 (by norm_num))
            (by nlinarith [hy'.2, Real.pi_pos])
        have hid :
            2 - 2 * Real.cos y - y * Real.sin y =
              2 * Real.sin (y / 2) * v15OdlyzkoR y := by
          rw [show y = 2 * (y / 2) by ring, Real.cos_two_mul_eq_one_sub,
            Real.sin_two_mul]
          simp only [v15OdlyzkoR]
          ring_nf
        rw [hid]
        positivity)
  have h := hmono (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx₀, hxπ⟩) hx₀
  simpa [v15OdlyzkoQ] using h

/-- The formula printed for `H` is nonnegative throughout its defining interval. -/
theorem v15OdlyzkoHCore_nonneg {t : ℝ} (ht₀ : 0 ≤ t) (ht₂ : t ≤ 2) :
    0 ≤ v15OdlyzkoHCore t := by
  by_cases ht₁ : t ≤ 1
  · have hfirst :
        0 ≤ (2 - t) * (1 + Real.cos (Real.pi * t) / 2) / 3 := by
      have hcos := Real.neg_one_le_cos (Real.pi * t)
      have hone : 0 ≤ 1 + Real.cos (Real.pi * t) / 2 := by linarith
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht₂) hone) (by norm_num)
    have harg₀ : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht₀
    have hargπ : Real.pi * t ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have hsecond : 0 ≤ Real.sin (Real.pi * t) / (2 * Real.pi) := by
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg₀ hargπ) (by positivity)
    exact add_nonneg hfirst hsecond
  · have ht₁' : 1 ≤ t := le_of_not_ge ht₁
    let y : ℝ := Real.pi * (2 - t)
    have hy₀ : 0 ≤ y := mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht₂)
    have hyπ : y ≤ Real.pi := by
      dsimp [y]
      nlinarith [Real.pi_pos]
    have hq : 0 ≤ v15OdlyzkoQ y := v15OdlyzkoQ_nonneg hy₀ hyπ
    have hangle : Real.pi * t = 2 * Real.pi - y := by
      dsimp [y]
      ring
    have hformula : v15OdlyzkoHCore t = v15OdlyzkoQ y / (6 * Real.pi) := by
      rw [v15OdlyzkoHCore, hangle, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
      dsimp [v15OdlyzkoQ, y]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hformula]
    exact div_nonneg hq (by positivity)

/-- `H` is an even function, as specified in the table description. -/
theorem v15OdlyzkoH_even (x : ℝ) : v15OdlyzkoH (-x) = v15OdlyzkoH x := by
  simp [v15OdlyzkoH]

/-- `H` vanishes outside `[-2, 2]`. -/
theorem v15OdlyzkoH_eq_zero_of_two_lt_abs {x : ℝ} (hx : 2 < |x|) :
    v15OdlyzkoH x = 0 := by
  simp [v15OdlyzkoH, not_le_of_gt hx]

/-- `H` is nonnegative on the whole real line. -/
theorem v15OdlyzkoH_nonneg (x : ℝ) : 0 ≤ v15OdlyzkoH x := by
  rw [v15OdlyzkoH]
  split_ifs with hx
  · exact v15OdlyzkoHCore_nonneg (abs_nonneg x) hx
  · exact le_rfl

/-- The formula on `[0, 2]` is continuous before applying the compact-support cutoff. -/
theorem v15OdlyzkoHCore_continuous : Continuous v15OdlyzkoHCore := by
  unfold v15OdlyzkoHCore
  fun_prop

/-- Odlyzko's auxiliary function is continuous across both support endpoints. -/
theorem v15OdlyzkoH_continuous : Continuous v15OdlyzkoH := by
  have hinside : Continuous (fun x : ℝ ↦ v15OdlyzkoHCore |x|) :=
    v15OdlyzkoHCore_continuous.comp continuous_abs
  unfold v15OdlyzkoH
  refine hinside.if ?_ continuous_const
  intro x hx
  have hset : {z : ℝ | |z| ≤ 2} = Set.Icc (-2) 2 := by
    ext z
    simp [abs_le]
  rw [hset, frontier_Icc (by norm_num)] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num

/-- Odlyzko's auxiliary function has compact support contained in `[-2, 2]`. -/
theorem v15OdlyzkoH_hasCompactSupport : HasCompactSupport v15OdlyzkoH := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-2) 2) isCompact_Icc
  intro x hx
  change -2 ≤ x ∧ x ≤ 2
  rw [← abs_le]
  by_contra hbound
  exact hx (v15OdlyzkoH_eq_zero_of_two_lt_abs (lt_of_not_ge hbound))

/-- Odlyzko's compactly supported auxiliary function is Lebesgue integrable. -/
theorem v15OdlyzkoH_integrable :
    MeasureTheory.Integrable v15OdlyzkoH MeasureTheory.volume :=
  v15OdlyzkoH_continuous.integrable_of_hasCompactSupport v15OdlyzkoH_hasCompactSupport

@[simp] theorem v15OdlyzkoH_zero : v15OdlyzkoH 0 = 1 := by
  norm_num [v15OdlyzkoH, v15OdlyzkoHCore]

@[simp] theorem v15OdlyzkoH_two : v15OdlyzkoH 2 = 0 := by
  simp [v15OdlyzkoH]

/-- The `b = 4` kernel is even. -/
theorem v15OdlyzkoF4_even (x : ℝ) : v15OdlyzkoF4 (-x) = v15OdlyzkoF4 x := by
  rw [v15OdlyzkoF4, v15OdlyzkoF4, show -x / 4 = -(x / 4) by ring,
    v15OdlyzkoH_even, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

/-- The `b = 4` kernel vanishes outside `[-8, 8]`. -/
theorem v15OdlyzkoF4_eq_zero_of_eight_lt_abs {x : ℝ} (hx : 8 < |x|) :
    v15OdlyzkoF4 x = 0 := by
  have hscaled : 2 < |x / 4| := by
    rw [abs_div]
    norm_num at hx ⊢
    linarith
  rw [v15OdlyzkoF4, v15OdlyzkoH_eq_zero_of_two_lt_abs hscaled, zero_div]

/-- The `b = 4` kernel is nonnegative. -/
theorem v15OdlyzkoF4_nonneg (x : ℝ) : 0 ≤ v15OdlyzkoF4 x := by
  exact div_nonneg (v15OdlyzkoH_nonneg (x / 4)) (Real.cosh_pos (x / 2)).le

/-- The unconditional `b = 4` kernel is continuous. -/
theorem v15OdlyzkoF4_continuous : Continuous v15OdlyzkoF4 := by
  unfold v15OdlyzkoF4
  exact (v15OdlyzkoH_continuous.comp (continuous_id.div_const 4)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

/-- The unconditional `b = 4` kernel has compact support contained in `[-8, 8]`. -/
theorem v15OdlyzkoF4_hasCompactSupport : HasCompactSupport v15OdlyzkoF4 := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-8) 8) isCompact_Icc
  intro x hx
  change -8 ≤ x ∧ x ≤ 8
  rw [← abs_le]
  by_contra hbound
  exact hx (v15OdlyzkoF4_eq_zero_of_eight_lt_abs (lt_of_not_ge hbound))

/-- The unconditional `b = 4` kernel is Lebesgue integrable. -/
theorem v15OdlyzkoF4_integrable :
    MeasureTheory.Integrable v15OdlyzkoF4 MeasureTheory.volume :=
  v15OdlyzkoF4_continuous.integrable_of_hasCompactSupport v15OdlyzkoF4_hasCompactSupport

@[simp] theorem v15OdlyzkoF4_zero : v15OdlyzkoF4 0 = 1 := by
  norm_num [v15OdlyzkoF4]

end

end TraceEuclidean
