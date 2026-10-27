import NormEuclidean.ChapterX.ScalarSUnitContraction
import NormEuclidean.NumberFieldNorm

/-!
# Integral perturbations with growth at an excluded infinite place

The infinite product formula equals the absolute field norm, which is at
least one for a nonzero algebraic integer. Contraction at every other
infinite place therefore bounds the excluded absolute value from below.
Multiplying by a sufficiently large natural number gives arbitrary growth
while preserving arbitrarily small finite and other-infinite coordinates.
-/

noncomputable section

namespace NormEuclidean.IntegralScalarGrowth

open IsDedekindDomain ScalarSUnitContraction
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

theorem infinite_product_ge_one (e : integerSubring K) (he : e ≠ 0) :
    1 ≤ ∏ w : NumberField.InfinitePlace K, w (e : K) ^ w.mult := by
  have heK : (e : K) ≠ 0 := by exact_mod_cast he
  have hn := integralNormMeasure_pos K e.property heK
  have hN : (1 : ℝ) ≤ integralNormMeasure K (e : K) := by exact_mod_cast hn
  have hs := integralNormMeasure_spec K (e : K) e.property
  have hnorm : |(Algebra.norm ℚ (e : K) : ℝ)| = integralNormMeasure K (e : K) := by
    exact_mod_cast hs.symm
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, Rat.cast_abs, hnorm]
  exact hN

/-- Integrality and contraction at all other infinite places force the
excluded absolute value to be at least one. Multiplicities are retained. -/
theorem one_le_at_excluded (e : integerSubring K) (he : e ≠ 0)
    (q : NumberField.InfinitePlace K)
    (hother : ∀ w : NumberField.InfinitePlace K, w ≠ q → w (e : K) ≤ 1) :
    1 ≤ q (e : K) := by
  classical
  by_contra! hq
  let f (w : NumberField.InfinitePlace K) := w (e : K) ^ w.mult
  have hrest : ∏ w ∈ Finset.univ.erase q, f w ≤ 1 := by
    apply Finset.prod_le_one
    · intro w _
      exact pow_nonneg (w.1.nonneg _) _
    · intro w hw
      exact pow_le_one₀ (w.1.nonneg _) (hother w (Finset.ne_of_mem_erase hw))
  have hqpow : f q < 1 := pow_lt_one₀ (q.1.nonneg _) hq
    NumberField.InfinitePlace.mult_ne_zero
  have hprod : (∏ w : NumberField.InfinitePlace K, f w) < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
    exact (mul_le_of_le_one_right (pow_nonneg (q.1.nonneg _) _) hrest).trans_lt hqpow
  exact not_lt_of_ge (infinite_product_ge_one e he) hprod

/-- An actual nonzero algebraic integer can be arbitrarily small at a
finite set of finite places and all other infinite places, while arbitrarily
large at the excluded infinite place. No growth principle is assumed. -/
theorem exists_large_perturbation (T : Finset (HeightOneSpectrum (integerSubring K)))
    (q : NumberField.InfinitePlace K) (γ : T → (ℤᵐ⁰)ˣ)
    (δ : NumberField.InfinitePlace K → ℝ) (hδ : ∀ w, w ≠ q → 0 < δ w) (B : ℝ) :
    ∃ p : integerSubring K, p ≠ 0 ∧
      (∀ v : T, v.1.intValuation p < γ v) ∧
      (∀ w : NumberField.InfinitePlace K, w ≠ q → w (p : K) < δ w) ∧
      B < q (p : K) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (max B 1)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans ((le_max_right B 1).trans_lt hn)
  have hn0 : (n : integerSubring K) ≠ 0 := by exact_mod_cast hnpos.ne'
  obtain ⟨e, he0, heT, _, heinf⟩ := exists_simultaneous_contraction T q γ
    (fun w ↦ min 1 (δ w / n)) (fun w hw ↦ lt_min zero_lt_one (div_pos (hδ w hw) hnpos))
  have heother (w : NumberField.InfinitePlace K) (hw : w ≠ q) : w (e : K) ≤ 1 :=
    (heinf w hw).le.trans (min_le_left _ _)
  have heq := one_le_at_excluded e he0 q heother
  let p : integerSubring K := n * e
  refine ⟨p, mul_ne_zero hn0 he0, ?_, ?_, ?_⟩
  · intro v
    dsimp only [p]
    rw [map_mul, mul_comm]
    exact (mul_le_of_le_one_right bot_le (v.1.intValuation_le_one n)).trans_lt (heT v)
  · intro w hw
    change w ((n : K) * (e : K)) < δ w
    rw [map_mul, w.map_natCast]
    have hsmall : w (e : K) < δ w / n := (heinf w hw).trans_le (min_le_right _ _)
    exact (mul_lt_mul_of_pos_left hsmall hnpos).trans_eq (by field_simp)
  · change B < q ((n : K) * (e : K))
    rw [map_mul, q.map_natCast]
    exact ((le_max_left B 1).trans_lt hn).trans_le
      (le_mul_of_one_le_right hnpos.le heq)

end NormEuclidean.IntegralScalarGrowth
