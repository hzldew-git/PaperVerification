import NormEuclidean.ChapterX.ExtensionIdeleNorm
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Local field norms detect valuation units

Integral norm boundedness and powers of a contracting element prove strict
contraction of its norm. This argument does not identify the normalizations
of the two absolute values. Applied to actual completed number fields it
shows that a unit-valued norm has a unit-valued preimage in each field factor.
The assertion is about one field factor, not a product of fields.
-/

noncomputable section

namespace NormEuclidean.LocalNormReflection

section Normed

variable {F E : Type*} [NontriviallyNormedField F] [NormedField E]
  [Algebra F E] [FiniteDimensional F E]

/-- Integral norm boundedness forces a strictly contracting element to have
a strictly contracting determinant norm. -/
theorem norm_lt_one_of_integral_bound
    (hbound : ∀ y : E, ‖y‖ ≤ 1 → ‖Algebra.norm F y‖ ≤ 1)
    {x : E} (hx : ‖x‖ < 1) : ‖Algebra.norm F x‖ < 1 := by
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one F
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  have haE : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr haE) hx
  have hy : ‖x ^ n / algebraMap F E a‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact (div_le_one (norm_pos_iff.mpr haE)).mpr hn.le
  have h := hbound (x ^ n / algebraMap F E a) hy
  rw [div_eq_mul_inv, map_mul, map_pow, Algebra.norm_inv,
    Algebra.norm_algebraMap, norm_mul, norm_inv, norm_pow, norm_pow] at h
  have hd : 0 < ‖a‖ ^ Module.finrank F E := pow_pos ha0 _
  have hlt : ‖Algebra.norm F x‖ ^ n < 1 := by
    have hle : ‖Algebra.norm F x‖ ^ n ≤ ‖a‖ ^ Module.finrank F E := by
      exact (div_le_one hd).mp (by simpa only [div_eq_mul_inv] using h)
    exact hle.trans_lt (pow_lt_one₀ (norm_nonneg a) ha1 Module.finrank_pos.ne')
  by_contra! hge
  exact (not_lt_of_ge (one_le_pow₀ hge)) hlt

/-- In a compact integral unit ball, norm-one is reflected by the determinant norm. -/
theorem norm_eq_one_iff_of_integral_bound
    (hbound : ∀ y : E, ‖y‖ ≤ 1 → ‖Algebra.norm F y‖ ≤ 1) (x : E) :
    ‖Algebra.norm F x‖ = 1 ↔ ‖x‖ = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · by_contra! hx
      have hi : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx
      have hn := norm_lt_one_of_integral_bound hbound hi
      rw [Algebra.norm_inv, norm_inv, h, inv_one] at hn
      exact (lt_irrefl 1) hn
    · by_contra! hx
      have hn := norm_lt_one_of_integral_bound hbound hx
      rw [h] at hn
      exact (lt_irrefl 1) hn
  · intro hx
    have hle := hbound x hx.le
    have hi := hbound x⁻¹ (by rw [norm_inv, hx, inv_one])
    rw [Algebra.norm_inv, norm_inv] at hi
    have hn0 : 0 < ‖Algebra.norm F x‖ := by
      apply norm_pos_iff.mpr
      exact (Algebra.norm_ne_zero_iff).mpr (norm_pos_iff.mp (by rw [hx]; exact zero_lt_one))
    exact le_antisymm hle ((inv_le_one₀ hn0).mp hi)

end Normed

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField WithZero

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- A single actual completed field norm reflects, as well as preserves,
valuation units. No split-place, ramification or residue-characteristic
hypothesis is required. -/
theorem finitePlaceAboveNormUnits_valuation_one_iff
    (p : HeightOneSpectrum (𝓞 K)) (w : FinitePlacesAbove (E := E) p)
    (z : (w.1.adicCompletion E)ˣ) :
    Valued.v ((finitePlaceAboveNormUnits p w z : (p.adicCompletion K)ˣ) :
      p.adicCompletion K) = 1 ↔ Valued.v (z : w.1.adicCompletion E) = 1 := by
  letI : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField (p.adicCompletion K) ℤᵐ⁰
  letI : NontriviallyNormedField (w.1.adicCompletion E) :=
    Valued.toNontriviallyNormedField (w.1.adicCompletion E) ℤᵐ⁰
  letI : Algebra (p.adicCompletion K) (w.1.adicCompletion E) := finitePlaceAboveAlgebra p w
  letI : ContinuousSMul (p.adicCompletion K) (w.1.adicCompletion E) :=
    ⟨((finitePlaceAboveCompletionMap_continuous p w).comp continuous_fst).mul
      continuous_snd⟩
  letI : Module.Finite (p.adicCompletion K) (w.1.adicCompletion E) :=
    finitePlaceAbove_moduleFinite p w
  have hb (y : w.1.adicCompletion E) (hy : ‖y‖ ≤ 1) :
      ‖Algebra.norm (p.adicCompletion K) y‖ ≤ 1 := by
    let S : Subring (w.1.adicCompletion E) := (w.1.adicCompletionIntegers E).toSubring
    letI : CompactSpace S := CompletionHensel.compact_completed_integers w.1
    exact LocalNormUnits.norm_le_one_on_compact_submonoid
      (Algebra.norm (p.adicCompletion K)) LocalNormUnits.continuous_algebra_norm
      S.toSubmonoid (isCompact_iff_compactSpace.mpr inferInstance)
      (Valued.toNormedField.norm_le_one_iff.mp hy)
  change Valued.v (Algebra.norm (p.adicCompletion K) (z : w.1.adicCompletion E)) = 1 ↔ _
  have hn := norm_eq_one_iff_of_integral_bound hb (z : w.1.adicCompletion E)
  simpa only [le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
    Valued.toNormedField.one_le_norm_iff] using hn

end NormEuclidean.LocalNormReflection
