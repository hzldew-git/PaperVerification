import NormEuclidean.RelativeZetaResidues
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Explicit CM normalization of the relative zeta residue

The maximal real subfield is used as the actual base field. The Hasse
unit index is the proved subgroup index, equal to one or two. The formula
keeps every archimedean, roots-of-unity and discriminant factor explicit.
No Brauer--Siegel or uniform discriminant-growth theorem is assumed.
-/

noncomputable section

namespace NormEuclidean.CMResidueComparison

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField Real

variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

set_option backward.isDefEq.respectTransparency false in
/-- A totally real field has only the two torsion units one and minus one. -/
theorem torsion_eq_one_or_neg_one (x : torsion F) :
    (x : (𝓞 F)ˣ) = 1 ∨ (x : (𝓞 F)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 F)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    have hzero := IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf (x.1 : F))
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    rw [IsTotallyReal.finrank F, hzero] at hpos
    exact (lt_irrefl 0 hpos).elim
  · interval_cases hi : orderOf (x : (𝓞 F)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

/-- The real base-field torsion factor in the class number formula is exactly two. -/
theorem torsionOrder_eq_two : torsionOrder F = 2 := by
  classical
  letI := Fintype.ofFinite (torsion F)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one F x

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

local notation "E⁺" => maximalRealSubfield E

/-- The actual number of complex places of a CM field equals the degree of its real subfield. -/
theorem complexPlaces_eq_real_degree : nrComplexPlaces E = Module.finrank ℚ E⁺ := by
  have h := (IsCMField.card_infinitePlace_eq_card_infinitePlace E).symm
  simpa only [card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero,
    zero_add, add_zero, ← IsTotallyReal.finrank] using h

/-- The unit-rank exponent is the real-subfield degree minus one. -/
theorem unitRank_eq_degree_sub_one : rank E = Module.finrank ℚ E⁺ - 1 := by
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, complexPlaces_eq_real_degree E]

/-- The regulator ratio is an actual proved CM unit-index formula, not a free parameter. -/
theorem regulator_ratio :
    regulator E / regulator E⁺ =
      2 ^ (Module.finrank ℚ E⁺ - 1) / IsCMField.indexRealUnits E := by
  rw [IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv,
    unitRank_eq_degree_sub_one, div_eq_mul_inv]

/-- The Hasse unit index which occurs in this normalization is positive and at most two. -/
theorem unitIndex_bounds :
    1 ≤ IsCMField.indexRealUnits E ∧ IsCMField.indexRealUnits E ≤ 2 := by
  rcases IsCMField.indexRealUnits_eq_one_or_two E with h | h <;> omega

/-- The relative value has the full CM class number normalization, with no hidden constant. -/
theorem relative_value_formula :
    RelativeZetaResidues.value E⁺ E =
      (2 * π) ^ Module.finrank ℚ E⁺ * (classNumber E : ℝ) * Real.sqrt |(discr E⁺ : ℝ)| /
        ((IsCMField.indexRealUnits E : ℝ) * torsionOrder E * classNumber E⁺ *
          Real.sqrt |(discr E : ℝ)|) := by
  have hRF : regulator E⁺ ≠ 0 := regulator_ne_zero E⁺
  have hw : (torsionOrder E : ℝ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero E
  have hh : (classNumber E⁺ : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos E⁺).ne'
  have hDF : Real.sqrt |(discr E⁺ : ℝ)| ≠ 0 :=
    (Real.sqrt_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero E⁺))).ne'
  have hDE : Real.sqrt |(discr E : ℝ)| ≠ 0 :=
    (Real.sqrt_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero E))).ne'
  have hI : (IsCMField.indexRealUnits E : ℝ) ≠ 0 := by
    have hb := (unitIndex_bounds E).1
    exact_mod_cast (show IsCMField.indexRealUnits E ≠ 0 by omega)
  have htwo : (2 : ℝ) ^ Module.finrank ℚ E⁺ ≠ 0 := by positivity
  have hdegree : 0 < Module.finrank ℚ E⁺ := Module.finrank_pos
  have hpow : (2 : ℝ) ^ (Module.finrank ℚ E⁺ - 1) * 2 =
      2 ^ Module.finrank ℚ E⁺ := by
    rw [← pow_succ, Nat.sub_add_cancel hdegree]
  have hratio : RelativeZetaResidues.value E⁺ E =
      π ^ Module.finrank ℚ E⁺ * (regulator E / regulator E⁺) * 2 *
        ((classNumber E : ℝ) / classNumber E⁺) / torsionOrder E *
          Real.sqrt |(discr E⁺ : ℝ)| / Real.sqrt |(discr E : ℝ)| := by
    rw [RelativeZetaResidues.value_formula,
      IsTotallyComplex.nrRealPlaces_eq_zero E, IsTotallyReal.nrComplexPlaces_eq_zero E⁺,
      complexPlaces_eq_real_degree E, ← IsTotallyReal.finrank E⁺, torsionOrder_eq_two E⁺]
    simp only [pow_zero, one_mul, mul_one]
    rw [mul_pow]
    field_simp [hRF, hw, hh, hDF, hDE, htwo]
    <;> ring
  rw [hratio, regulator_ratio E, mul_pow, ← hpow]
  field_simp [hRF, hw, hh, hDF, hDE, hI]
  <;> ring

end NormEuclidean.CMResidueComparison
