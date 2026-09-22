import TraceEuclidean.V15OdlyzkoKernel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Autocorrelation representation of Odlyzko's auxiliary function

The unconditional auxiliary function `H` is the normalized autocorrelation
of the compactly supported bump `1 + cos (π x)` on `[-1, 1]`.  This file
proves that identity from an exact interval integral.  It supplies the
structural input for a later Fourier-transform positivity proof.
-/

namespace TraceEuclidean
noncomputable section
open intervalIntegral
open MeasureTheory
open scoped Convolution

/-- The elementary bump before applying its support cutoff. -/
def v15OdlyzkoBumpCore (t : ℝ) : ℝ := 1 + Real.cos (Real.pi * t)

private def v15OdlyzkoBumpPrimitive (x t : ℝ) : ℝ :=
  t + Real.sin (Real.pi * t) / Real.pi +
    Real.sin (Real.pi * (t - x)) / Real.pi +
    t * Real.cos (Real.pi * x) / 2 +
    Real.sin (Real.pi * (2 * t - x)) / (4 * Real.pi)

private theorem v15OdlyzkoBumpPrimitive_hasDerivAt (x t : ℝ) :
    HasDerivAt (v15OdlyzkoBumpPrimitive x)
      (v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (t - x)) t := by
  have hsinOne : HasDerivAt (fun y : ℝ => Real.sin (Real.pi * y))
      (Real.cos (Real.pi * t) * Real.pi) t := by
    convert (Real.hasDerivAt_sin (Real.pi * t)).comp t
      ((hasDerivAt_id t).const_mul Real.pi) using 1
    all_goals first | (with_reducible_and_instances rfl) | (funext y; rfl) | ring
  have hsinShift : HasDerivAt (fun y : ℝ => Real.sin (Real.pi * (y - x)))
      (Real.cos (Real.pi * (t - x)) * Real.pi) t := by
    convert (Real.hasDerivAt_sin (Real.pi * (t - x))).comp t
      (((hasDerivAt_id t).sub_const x).const_mul Real.pi) using 1
    all_goals first | (with_reducible_and_instances rfl) | (funext y; rfl) | ring
  have hsinDouble : HasDerivAt (fun y : ℝ => Real.sin (Real.pi * (2 * y - x)))
      (Real.cos (Real.pi * (2 * t - x)) * (Real.pi * 2)) t := by
    convert (Real.hasDerivAt_sin (Real.pi * (2 * t - x))).comp t
      ((((hasDerivAt_id t).const_mul 2).sub_const x).const_mul Real.pi) using 1
    all_goals first | (with_reducible_and_instances rfl) | (funext y; rfl) | ring
  have hraw : HasDerivAt (v15OdlyzkoBumpPrimitive x)
      (1 + (Real.cos (Real.pi * t) * Real.pi) / Real.pi +
        (Real.cos (Real.pi * (t - x)) * Real.pi) / Real.pi +
        (1 * Real.cos (Real.pi * x)) / 2 +
        (Real.cos (Real.pi * (2 * t - x)) * (Real.pi * 2)) /
          (4 * Real.pi)) t := by
    unfold v15OdlyzkoBumpPrimitive
    convert (((((hasDerivAt_id t).add (hsinOne.div_const Real.pi)).add
      (hsinShift.div_const Real.pi)).add
      (((hasDerivAt_id t).mul_const (Real.cos (Real.pi * x))).div_const 2)).add
      (hsinDouble.div_const (4 * Real.pi))) using 1
    all_goals first | (with_reducible_and_instances rfl) | (funext y; rfl)
  convert hraw using 1
  · have htrig := Real.two_mul_cos_mul_cos
      (Real.pi * t) (Real.pi * (t - x))
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    unfold v15OdlyzkoBumpCore
    rw [show Real.pi * t - Real.pi * (t - x) = Real.pi * x by ring,
      show Real.pi * t + Real.pi * (t - x) = Real.pi * (2 * t - x) by ring] at htrig
    field_simp [hpi]
    ring_nf at htrig ⊢
    nlinarith [htrig]

private theorem v15OdlyzkoBumpPrimitive_endpoint_sub (x : ℝ) :
    v15OdlyzkoBumpPrimitive x 1 - v15OdlyzkoBumpPrimitive x (x - 1) =
      3 * v15OdlyzkoHCore x := by
  unfold v15OdlyzkoBumpPrimitive v15OdlyzkoHCore
  rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
    Real.sin_pi_sub,
    show Real.pi * (2 * 1 - x) = 2 * Real.pi - Real.pi * x by ring,
    Real.sin_two_pi_sub,
    show Real.pi * (x - 1) = Real.pi * x - Real.pi by ring,
    Real.sin_sub_pi,
    show Real.pi * (x - 1 - x) = -Real.pi by ring,
    Real.sin_neg, Real.sin_pi, neg_zero,
    show Real.pi * (2 * (x - 1) - x) = Real.pi * x - 2 * Real.pi by ring,
    Real.sin_sub_two_pi,
    show Real.pi * 1 = Real.pi by ring, Real.sin_pi]
  field_simp [Real.pi_ne_zero]
  ring

/-- On an overlap interval, the autocorrelation integral evaluates exactly to
the formula printed by Odlyzko for `H`. -/
theorem v15OdlyzkoHCore_eq_overlapIntegral (x : ℝ) :
    v15OdlyzkoHCore x =
      (1 / 3 : ℝ) * ∫ t in (x - 1)..1, v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (t - x) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (t - x))
      MeasureTheory.volume (x - 1) 1 := by
    apply Continuous.intervalIntegrable
    unfold v15OdlyzkoBumpCore
    fun_prop
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := v15OdlyzkoBumpPrimitive x)
    (fun t _ ↦ v15OdlyzkoBumpPrimitive_hasDerivAt x t) hint
  rw [hfund, v15OdlyzkoBumpPrimitive_endpoint_sub]
  ring

/-- The compactly supported bump whose normalized autocorrelation is `H`. -/
def v15OdlyzkoBump (t : ℝ) : ℝ :=
  if |t| ≤ 1 then v15OdlyzkoBumpCore t else 0

private theorem v15OdlyzkoBumpCore_even (t : ℝ) :
    v15OdlyzkoBumpCore (-t) = v15OdlyzkoBumpCore t := by
  unfold v15OdlyzkoBumpCore
  rw [show Real.pi * -t = -(Real.pi * t) by ring, Real.cos_neg]

/-- The bump vanishes at and outside both support endpoints. -/
theorem v15OdlyzkoBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) :
    v15OdlyzkoBump t = 0 := by
  unfold v15OdlyzkoBump
  split_ifs with hle
  · have heq : |t| = 1 := le_antisymm hle ht
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with rfl | rfl
    · simp [v15OdlyzkoBumpCore]
    · simp [v15OdlyzkoBumpCore]
  · rfl

private theorem v15OdlyzkoBump_product_indicator
    {x : ℝ} (hx₀ : 0 ≤ x) :
    (fun t ↦ v15OdlyzkoBump t * v15OdlyzkoBump (x - t)) =
      (Set.Ioc (x - 1) 1).indicator
        (fun t ↦ v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (x - t)) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (x - 1) 1
  · have htOne : |t| ≤ 1 := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
    have hxtOne : |x - t| ≤ 1 := (abs_le).2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp [Set.indicator_of_mem ht, v15OdlyzkoBump, htOne, hxtOne]
  · simp only [Set.indicator, ht, if_false]
    by_cases htAbs : 1 ≤ |t|
    · rw [v15OdlyzkoBump_eq_zero_of_one_le_abs htAbs, zero_mul]
    · have htBounds : -1 < t ∧ t < 1 := (abs_lt).mp (lt_of_not_ge htAbs)
      have htLow : t ≤ x - 1 := by
        by_contra hlt
        exact ht ⟨lt_of_not_ge hlt, htBounds.2.le⟩
      have hxt : 1 ≤ |x - t| :=
        (show 1 ≤ x - t by linarith).trans (le_abs_self (x - t))
      rw [v15OdlyzkoBump_eq_zero_of_one_le_abs hxt, mul_zero]

/-- The normalized convolution square of the compactly supported bump. -/
def v15OdlyzkoHAutocorrelation (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) *
    (v15OdlyzkoBump ⋆[ContinuousLinearMap.mul ℝ ℝ] v15OdlyzkoBump) x

private theorem v15OdlyzkoHAutocorrelation_eq_core
    {x : ℝ} (hx₀ : 0 ≤ x) (hx₂ : x ≤ 2) :
    v15OdlyzkoHAutocorrelation x = v15OdlyzkoHCore x := by
  unfold v15OdlyzkoHAutocorrelation
  rw [MeasureTheory.convolution_mul]
  rw [v15OdlyzkoBump_product_indicator hx₀,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx₂] : x - 1 ≤ (1 : ℝ))]
  have heven :
      (∫ t in (x - 1)..1, v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (x - t)) =
        ∫ t in (x - 1)..1, v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (t - x) := by
    apply intervalIntegral.integral_congr
    intro t _
    change v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (x - t) =
      v15OdlyzkoBumpCore t * v15OdlyzkoBumpCore (t - x)
    rw [← v15OdlyzkoBumpCore_even (t - x), show -(t - x) = x - t by ring]
  rw [heven, ← v15OdlyzkoHCore_eq_overlapIntegral]

/-- The compactly supported generating bump is even. -/
theorem v15OdlyzkoBump_even (t : ℝ) :
    v15OdlyzkoBump (-t) = v15OdlyzkoBump t := by
  unfold v15OdlyzkoBump
  rw [abs_neg]
  split_ifs
  · exact v15OdlyzkoBumpCore_even t
  · rfl

/-- The generating bump is continuous across its support endpoints. -/
theorem v15OdlyzkoBump_continuous : Continuous v15OdlyzkoBump := by
  have hinside : Continuous v15OdlyzkoBumpCore := by
    unfold v15OdlyzkoBumpCore
    fun_prop
  unfold v15OdlyzkoBump
  refine hinside.if ?_ continuous_const
  intro x hx
  have hset : {z : ℝ | |z| ≤ 1} = Set.Icc (-1) 1 := by
    ext z
    simp [abs_le]
  rw [hset, frontier_Icc (by norm_num)] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num [v15OdlyzkoBumpCore]

/-- The generating bump has compact support contained in `[-1, 1]`. -/
theorem v15OdlyzkoBump_hasCompactSupport : HasCompactSupport v15OdlyzkoBump := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1) 1) isCompact_Icc
  intro x hx
  change -1 ≤ x ∧ x ≤ 1
  rw [← abs_le]
  by_contra hbound
  exact hx (v15OdlyzkoBump_eq_zero_of_one_le_abs (le_of_not_ge hbound))

/-- The generating bump is Lebesgue integrable. -/
theorem v15OdlyzkoBump_integrable :
    MeasureTheory.Integrable v15OdlyzkoBump MeasureTheory.volume :=
  v15OdlyzkoBump_continuous.integrable_of_hasCompactSupport
    v15OdlyzkoBump_hasCompactSupport

private theorem v15OdlyzkoHAutocorrelation_even (x : ℝ) :
    v15OdlyzkoHAutocorrelation (-x) = v15OdlyzkoHAutocorrelation x := by
  unfold v15OdlyzkoHAutocorrelation
  rw [MeasureTheory.convolution_neg_of_neg_eq
    (ContinuousLinearMap.mul ℝ ℝ)
    (Filter.Eventually.of_forall v15OdlyzkoBump_even)
    (Filter.Eventually.of_forall v15OdlyzkoBump_even)]

private theorem v15OdlyzkoHAutocorrelation_eq_zero_of_two_lt
    {x : ℝ} (hx : 2 < x) : v15OdlyzkoHAutocorrelation x = 0 := by
  unfold v15OdlyzkoHAutocorrelation
  rw [MeasureTheory.convolution_mul]
  have hz : ∀ t : ℝ, v15OdlyzkoBump t * v15OdlyzkoBump (x - t) = 0 := by
    intro t
    by_cases ht : 1 ≤ |t|
    · rw [v15OdlyzkoBump_eq_zero_of_one_le_abs ht, zero_mul]
    · have htOne : t < 1 := (abs_lt.mp (lt_of_not_ge ht)).2
      have hxt : 1 ≤ |x - t| :=
        (show 1 ≤ x - t by linarith).trans (le_abs_self (x - t))
      rw [v15OdlyzkoBump_eq_zero_of_one_le_abs hxt, mul_zero]
  simp_rw [hz, MeasureTheory.integral_zero, mul_zero]

/-- Odlyzko's auxiliary function is exactly the normalized autocorrelation of
the compactly supported bump. -/
theorem v15OdlyzkoH_eq_autocorrelation (x : ℝ) :
    v15OdlyzkoH x = v15OdlyzkoHAutocorrelation x := by
  by_cases hxSupport : |x| ≤ 2
  · by_cases hx₀ : 0 ≤ x
    · rw [v15OdlyzkoH, if_pos hxSupport, abs_of_nonneg hx₀,
        v15OdlyzkoHAutocorrelation_eq_core hx₀ (by simpa [abs_of_nonneg hx₀] using hxSupport)]
    · have hneg : 0 ≤ -x := by linarith
      have hnegTwo : -x ≤ 2 := by
        rw [abs_of_neg (lt_of_not_ge hx₀)] at hxSupport
        exact hxSupport
      have hnegEq : v15OdlyzkoH (-x) = v15OdlyzkoHAutocorrelation (-x) := by
        rw [v15OdlyzkoH, if_pos (by simpa using hxSupport), abs_of_nonneg hneg,
          v15OdlyzkoHAutocorrelation_eq_core hneg hnegTwo]
      exact (v15OdlyzkoH_even x).symm.trans
        (hnegEq.trans (v15OdlyzkoHAutocorrelation_even x))
  · have hxAbs : 2 < |x| := lt_of_not_ge hxSupport
    rw [v15OdlyzkoH_eq_zero_of_two_lt_abs hxAbs]
    by_cases hx₀ : 0 ≤ x
    · exact (v15OdlyzkoHAutocorrelation_eq_zero_of_two_lt
        (by simpa [abs_of_nonneg hx₀] using hxAbs)).symm
    · symm
      exact (v15OdlyzkoHAutocorrelation_even x).symm.trans
        (v15OdlyzkoHAutocorrelation_eq_zero_of_two_lt
          (by simpa [abs_of_neg (lt_of_not_ge hx₀)] using hxAbs))


end
end TraceEuclidean
