import TraceEuclidean.PoitouKernel
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Compact bump underlying Poitou's test function

This module adds the support cutoff to Poitou's polynomial bump, identifies
its angular-frequency cosine transform with `poitouAmplitude`, and computes
the exact squared mass `3 / 5`.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory intervalIntegral FourierTransform Complex
open scoped RealInnerProductSpace

/-- The compactly supported normalized quadratic bump. -/
def poitouBump (t : ℝ) : ℝ :=
  if |t| ≤ 1 then poitouBumpCore t else 0

private theorem poitouBumpCore_even (t : ℝ) :
    poitouBumpCore (-t) = poitouBumpCore t := by
  unfold poitouBumpCore
  ring

/-- The Poitou bump vanishes at and outside its support endpoints. -/
theorem poitouBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) :
    poitouBump t = 0 := by
  unfold poitouBump
  split_ifs with hle
  · have heq : |t| = 1 := le_antisymm hle ht
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with rfl | rfl <;>
      norm_num [poitouBumpCore]
  · rfl

/-- The compact bump is even. -/
theorem poitouBump_even (t : ℝ) : poitouBump (-t) = poitouBump t := by
  unfold poitouBump
  rw [abs_neg]
  split_ifs
  · exact poitouBumpCore_even t
  · rfl

/-- The compact bump is pointwise nonnegative. -/
theorem poitouBump_nonneg (t : ℝ) : 0 ≤ poitouBump t := by
  unfold poitouBump
  split_ifs with ht
  · have htSq : t ^ 2 ≤ 1 := by
      have hp := pow_le_pow_left₀ (abs_nonneg t) ht 2
      simpa only [sq_abs, one_pow] using hp
    unfold poitouBumpCore
    positivity
  · exact le_rfl

/-- The support cutoff remains continuous because the polynomial vanishes at
both endpoints. -/
theorem poitouBump_continuous : Continuous poitouBump := by
  have hinside : Continuous poitouBumpCore := by
    unfold poitouBumpCore
    fun_prop
  unfold poitouBump
  refine hinside.if ?_ continuous_const
  intro x hx
  have hset : {z : ℝ | |z| ≤ 1} = Set.Icc (-1) 1 := by
    ext z
    simp [abs_le]
  rw [hset, frontier_Icc (by norm_num)] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num [poitouBumpCore]

/-- The Poitou bump has compact support in `[-1,1]`. -/
theorem poitouBump_hasCompactSupport : HasCompactSupport poitouBump := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1) 1) isCompact_Icc
  intro x hx
  change -1 ≤ x ∧ x ≤ 1
  rw [← abs_le]
  by_contra hbound
  exact hx (poitouBump_eq_zero_of_one_le_abs (le_of_not_ge hbound))

/-- The compact Poitou bump is Lebesgue integrable. -/
theorem poitouBump_integrable : Integrable poitouBump volume :=
  poitouBump_continuous.integrable_of_hasCompactSupport
    poitouBump_hasCompactSupport

private theorem poitouBump_mul_eq_indicator (x : ℝ) :
    (fun t : ℝ ↦ poitouBump t * Real.cos (x * t)) =
      (Set.Ioc (-1 : ℝ) 1).indicator
        (fun t : ℝ ↦ poitouBumpCore t * Real.cos (x * t)) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (-1 : ℝ) 1
  · have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    simp [poitouBump, habs, Set.indicator_of_mem ht]
  · simp only [Set.indicator, ht, if_false]
    unfold poitouBump
    split_ifs with habs
    · have hb := abs_le.mp habs
      have hleft : t = -1 := by
        have hnotLeft : ¬ (-1 : ℝ) < t := by
          intro hlt
          exact ht ⟨hlt, hb.2⟩
        exact le_antisymm (le_of_not_gt hnotLeft) hb.1
      subst t
      norm_num [poitouBumpCore]
    · simp

/-- The compact-support integral is the amplitude used in the source. -/
theorem poitouAmplitude_eq_integral_bump_cos (x : ℝ) :
    poitouAmplitude x =
      ∫ t : ℝ, poitouBump t * Real.cos (x * t) := by
  rw [poitouAmplitude, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    poitouBump_mul_eq_indicator, MeasureTheory.integral_indicator measurableSet_Ioc]

/-- The square of the compact bump has exact mass `3 / 5`. -/
theorem poitouBump_sq_integral :
    (∫ t : ℝ, poitouBump t ^ 2) = 3 / 5 := by
  have hfun : (fun t : ℝ ↦ poitouBump t ^ 2) =
      (Set.Ioc (-1 : ℝ) 1).indicator (fun t : ℝ ↦ poitouBumpCore t ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (-1 : ℝ) 1
    · have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
      simp [poitouBump, habs, Set.indicator_of_mem ht]
    · simp only [Set.indicator, ht, if_false]
      unfold poitouBump
      split_ifs with habs
      · have hb := abs_le.mp habs
        have hleft : t = -1 := by
          have hnotLeft : ¬ (-1 : ℝ) < t := by
            intro hlt
            exact ht ⟨hlt, hb.2⟩
          exact le_antisymm (le_of_not_gt hnotLeft) hb.1
        subst t
        norm_num [poitouBumpCore]
      · simp
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hpoly : (fun t : ℝ ↦ poitouBumpCore t ^ 2) =
      (fun t : ℝ ↦ (9 / 16 : ℝ) * (1 - 2 * t ^ 2 + t ^ 4)) := by
    funext t
    unfold poitouBumpCore
    ring
  rw [hpoly]
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable (-1) 1
  have hquad : IntervalIntegrable (fun t : ℝ ↦ (-2 : ℝ) * t ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hquart : IntervalIntegrable (fun t : ℝ ↦ t ^ 4) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplit :
      (∫ t : ℝ in (-1)..1, 1 - 2 * t ^ 2 + t ^ 4) =
        (∫ t : ℝ in (-1)..1, 1) +
          (∫ t : ℝ in (-1)..1, (-2 : ℝ) * t ^ 2) +
            ∫ t : ℝ in (-1)..1, t ^ 4 := by
    rw [← intervalIntegral.integral_add hconst hquad,
      ← intervalIntegral.integral_add (hconst.add hquad) hquart]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [intervalIntegral.integral_const_mul, hsplit,
    intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

/-- Complex-valued version of the compact bump. -/
def poitouBumpComplex (t : ℝ) : ℂ := poitouBump t

theorem poitouBumpComplex_integrable : Integrable poitouBumpComplex volume :=
  poitouBump_integrable.ofReal

theorem poitouBumpComplex_continuous : Continuous poitouBumpComplex := by
  change Continuous (Complex.ofReal ∘ poitouBump)
  exact Complex.continuous_ofReal.comp poitouBump_continuous

theorem poitouBumpComplex_even (t : ℝ) :
    poitouBumpComplex (-t) = poitouBumpComplex t := by
  simp [poitouBumpComplex, poitouBump_even]

end

end TraceEuclidean.PoitouKernel
