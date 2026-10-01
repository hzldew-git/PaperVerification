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

in the unconditional explicit formula.  The paper  uses the row `b = 4`.
The analytic explicit formula and the archimedean integral estimates are not
claimed here.
-/

namespace TraceEuclidean

noncomputable section

/-- The formula for Odlyzko's unconditional auxiliary function on `[0, 2]`. -/
def odlyzkoHCore (t : ℝ) : ℝ :=
  (2 - t) * (1 + Real.cos (Real.pi * t) / 2) / 3 +
    Real.sin (Real.pi * t) / (2 * Real.pi)

/-- Odlyzko's even compactly supported auxiliary function `H`. -/
def odlyzkoH (x : ℝ) : ℝ :=
  if |x| ≤ 2 then odlyzkoHCore |x| else 0

/-- The unconditional Odlyzko kernel for the Table 4 row `b = 4`. -/
def odlyzkoF4 (x : ℝ) : ℝ :=
  odlyzkoH (x / 4) / Real.cosh (x / 2)

@[simp] theorem odlyzkoHCore_two : odlyzkoHCore 2 = 0 := by
  rw [odlyzkoHCore, show Real.pi * 2 = 2 * Real.pi by ring,
    Real.cos_two_pi, Real.sin_two_pi]
  norm_num

private def odlyzkoR (x : ℝ) : ℝ :=
  2 * Real.sin (x / 2) - x * Real.cos (x / 2)

private def odlyzkoQ (x : ℝ) : ℝ :=
  x * (2 + Real.cos x) - 3 * Real.sin x

private theorem odlyzkoR_hasDerivAt (x : ℝ) :
    HasDerivAt odlyzkoR (x / 2 * Real.sin (x / 2)) x := by
  unfold odlyzkoR
  convert
    (((Real.hasDerivAt_sin (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).const_mul 2).sub
      ((hasDerivAt_id x).mul
        ((Real.hasDerivAt_cos (x / 2)).comp x ((hasDerivAt_id x).div_const 2))) using 1
  all_goals first | rfl | (simp only [Function.comp_apply, id_eq]; ring_nf)

private theorem odlyzkoR_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ odlyzkoR x := by
  have hmono : MonotoneOn odlyzkoR (Set.Icc 0 Real.pi) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi) (by
      unfold odlyzkoR
      fun_prop)
      (fun y _ ↦ (odlyzkoR_hasDerivAt y).hasDerivWithinAt) (by
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) Real.pi := interior_subset hy
        exact mul_nonneg (div_nonneg hy'.1 (by norm_num))
          (Real.sin_nonneg_of_nonneg_of_le_pi
            (div_nonneg hy'.1 (by norm_num)) (by nlinarith [hy'.2, Real.pi_pos])))
  have h := hmono (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx₀, hxπ⟩) hx₀
  simpa [odlyzkoR] using h

private theorem odlyzkoQ_hasDerivAt (x : ℝ) :
    HasDerivAt odlyzkoQ (2 - 2 * Real.cos x - x * Real.sin x) x := by
  unfold odlyzkoQ
  convert
    ((hasDerivAt_id x).mul
      ((hasDerivAt_const x 2).add (Real.hasDerivAt_cos x))).sub
      ((Real.hasDerivAt_sin x).const_mul 3) using 1
  all_goals first | rfl | (simp only [Pi.add_apply, id_eq]; ring_nf)

private theorem odlyzkoQ_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ odlyzkoQ x := by
  have hmono : MonotoneOn odlyzkoQ (Set.Icc 0 Real.pi) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi) (by
      unfold odlyzkoQ
      fun_prop)
      (fun y _ ↦ (odlyzkoQ_hasDerivAt y).hasDerivWithinAt) (by
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) Real.pi := interior_subset hy
        have hr : 0 ≤ odlyzkoR y := odlyzkoR_nonneg hy'.1 hy'.2
        have hs : 0 ≤ Real.sin (y / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg hy'.1 (by norm_num))
            (by nlinarith [hy'.2, Real.pi_pos])
        have hid :
            2 - 2 * Real.cos y - y * Real.sin y =
              2 * Real.sin (y / 2) * odlyzkoR y := by
          rw [show y = 2 * (y / 2) by ring, Real.cos_two_mul_eq_one_sub,
            Real.sin_two_mul]
          simp only [odlyzkoR]
          ring_nf
        rw [hid]
        positivity)
  have h := hmono (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx₀, hxπ⟩) hx₀
  simpa [odlyzkoQ] using h

/-- The formula printed for `H` is nonnegative throughout its defining interval. -/
theorem odlyzkoHCore_nonneg {t : ℝ} (ht₀ : 0 ≤ t) (ht₂ : t ≤ 2) :
    0 ≤ odlyzkoHCore t := by
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
    have hq : 0 ≤ odlyzkoQ y := odlyzkoQ_nonneg hy₀ hyπ
    have hangle : Real.pi * t = 2 * Real.pi - y := by
      dsimp [y]
      ring
    have hformula : odlyzkoHCore t = odlyzkoQ y / (6 * Real.pi) := by
      rw [odlyzkoHCore, hangle, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
      dsimp [odlyzkoQ, y]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hformula]
    exact div_nonneg hq (by positivity)

/-- `H` is an even function, as specified in the table description. -/
theorem odlyzkoH_even (x : ℝ) : odlyzkoH (-x) = odlyzkoH x := by
  simp [odlyzkoH]

/-- `H` vanishes outside `[-2, 2]`. -/
theorem odlyzkoH_eq_zero_of_two_lt_abs {x : ℝ} (hx : 2 < |x|) :
    odlyzkoH x = 0 := by
  simp [odlyzkoH, not_le_of_gt hx]

/-- `H` is nonnegative on the whole real line. -/
theorem odlyzkoH_nonneg (x : ℝ) : 0 ≤ odlyzkoH x := by
  rw [odlyzkoH]
  split_ifs with hx
  · exact odlyzkoHCore_nonneg (abs_nonneg x) hx
  · exact le_rfl

/-- The formula on `[0, 2]` is continuous before applying the compact-support cutoff. -/
theorem odlyzkoHCore_continuous : Continuous odlyzkoHCore := by
  unfold odlyzkoHCore
  fun_prop

/-- Odlyzko's auxiliary function is continuous across both support endpoints. -/
theorem odlyzkoH_continuous : Continuous odlyzkoH := by
  have hinside : Continuous (fun x : ℝ ↦ odlyzkoHCore |x|) :=
    odlyzkoHCore_continuous.comp continuous_abs
  unfold odlyzkoH
  refine hinside.if ?_ continuous_const
  intro x hx
  have hset : {z : ℝ | |z| ≤ 2} = Set.Icc (-2) 2 := by
    ext z
    simp [abs_le]
  rw [hset, frontier_Icc (by norm_num)] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num

/-- Odlyzko's auxiliary function has compact support contained in `[-2, 2]`. -/
theorem odlyzkoH_hasCompactSupport : HasCompactSupport odlyzkoH := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-2) 2) isCompact_Icc
  intro x hx
  change -2 ≤ x ∧ x ≤ 2
  rw [← abs_le]
  by_contra hbound
  exact hx (odlyzkoH_eq_zero_of_two_lt_abs (lt_of_not_ge hbound))

/-- Odlyzko's compactly supported auxiliary function is Lebesgue integrable. -/
theorem odlyzkoH_integrable :
    MeasureTheory.Integrable odlyzkoH MeasureTheory.volume :=
  odlyzkoH_continuous.integrable_of_hasCompactSupport odlyzkoH_hasCompactSupport

@[simp] theorem odlyzkoH_zero : odlyzkoH 0 = 1 := by
  norm_num [odlyzkoH, odlyzkoHCore]

@[simp] theorem odlyzkoH_two : odlyzkoH 2 = 0 := by
  simp [odlyzkoH]

/-- The `b = 4` kernel is even. -/
theorem odlyzkoF4_even (x : ℝ) : odlyzkoF4 (-x) = odlyzkoF4 x := by
  rw [odlyzkoF4, odlyzkoF4, show -x / 4 = -(x / 4) by ring,
    odlyzkoH_even, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

/-- The `b = 4` kernel vanishes outside `[-8, 8]`. -/
theorem odlyzkoF4_eq_zero_of_eight_lt_abs {x : ℝ} (hx : 8 < |x|) :
    odlyzkoF4 x = 0 := by
  have hscaled : 2 < |x / 4| := by
    rw [abs_div]
    norm_num at hx ⊢
    linarith
  rw [odlyzkoF4, odlyzkoH_eq_zero_of_two_lt_abs hscaled, zero_div]

/-- The `b = 4` kernel is nonnegative. -/
theorem odlyzkoF4_nonneg (x : ℝ) : 0 ≤ odlyzkoF4 x := by
  exact div_nonneg (odlyzkoH_nonneg (x / 4)) (Real.cosh_pos (x / 2)).le

/-- The unconditional `b = 4` kernel is continuous. -/
theorem odlyzkoF4_continuous : Continuous odlyzkoF4 := by
  unfold odlyzkoF4
  exact (odlyzkoH_continuous.comp (continuous_id.div_const 4)).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

/-- The unconditional `b = 4` kernel has compact support contained in `[-8, 8]`. -/
theorem odlyzkoF4_hasCompactSupport : HasCompactSupport odlyzkoF4 := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-8) 8) isCompact_Icc
  intro x hx
  change -8 ≤ x ∧ x ≤ 8
  rw [← abs_le]
  by_contra hbound
  exact hx (odlyzkoF4_eq_zero_of_eight_lt_abs (lt_of_not_ge hbound))

/-- The unconditional `b = 4` kernel is Lebesgue integrable. -/
theorem odlyzkoF4_integrable :
    MeasureTheory.Integrable odlyzkoF4 MeasureTheory.volume :=
  odlyzkoF4_continuous.integrable_of_hasCompactSupport odlyzkoF4_hasCompactSupport

@[simp] theorem odlyzkoF4_zero : odlyzkoF4 0 = 1 := by
  norm_num [odlyzkoF4]

end

end TraceEuclidean
