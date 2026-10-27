import NormEuclidean.ChapterX.LocalNormIndices
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Quadratic norm indices at infinite completions

Real nonsplit norms are precisely the positive units, and every complex
unit is a square. Ring equivalences transport these computations to the
actual infinite completions and their extension norm fibers.
-/

noncomputable section

namespace NormEuclidean.InfiniteNormIndices

open Bong.Dyadic IsDedekindDomain QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField

/-- A ring equivalence preserves the actual quadratic norm equation. -/
theorem norm_map_iff {F E : Type*} [Field F] [Field E] (e : F ≃+* E)
    (theta a : Fˣ) :
    IsQuadraticNorm E (Units.map e.toMonoidHom theta) (Units.map e.toMonoidHom a) ↔
      IsQuadraticNorm F theta a := by
  have he (z : F) : e.toMonoidHom z = e z := rfl
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨e.symm x, e.symm y, e.injective ?_⟩
    simpa only [map_sub, map_mul, map_pow, e.apply_symm_apply, Units.coe_map, he] using h
  · rintro ⟨x, y, h⟩
    refine ⟨e x, e y, ?_⟩
    simpa only [map_sub, map_pow, map_mul, Units.coe_map, he] using congrArg e h

/-- The corresponding norm subgroup indices agree across a ring equivalence. -/
theorem index_map (F E : Type*) [Field F] [Field E] (e : F ≃+* E) (theta : Fˣ) :
    (quadraticNormGroup F theta).index =
      (quadraticNormGroup E (Units.map e.toMonoidHom theta)).index := by
  let f := Units.mapEquiv e.toMulEquiv
  have heq : quadraticNormGroup F theta =
      (quadraticNormGroup E (Units.map e.toMonoidHom theta)).comap f.toMonoidHom := by
    ext a
    exact (norm_map_iff e theta a).symm
  rw [heq]
  exact Subgroup.index_comap_of_surjective _ f.surjective

/-- A nonnegative nonzero real number is a square in the unit group. -/
theorem real_isSquare_of_nonneg (a : ℝˣ) (ha : 0 ≤ a.val) : IsSquare a := by
  have hs := Real.sq_sqrt ha
  have hz : Real.sqrt a.val ≠ 0 := by
    intro h
    exact a.ne_zero (by simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hs.symm)
  refine ⟨Units.mk0 (Real.sqrt a.val) hz, Units.ext ?_⟩
  change a.val = Real.sqrt a.val * Real.sqrt a.val
  simpa only [← pow_two] using hs.symm

/-- For a negative real parameter, the nonzero norms are exactly positive. -/
theorem real_norm_iff_positive (theta : ℝˣ) (htheta : theta.val < 0) (a : ℝˣ) :
    IsQuadraticNorm ℝ theta a ↔ 0 < a.val := by
  constructor
  · rintro ⟨x, y, h⟩
    have hm := mul_nonpos_of_nonpos_of_nonneg htheta.le (sq_nonneg y)
    have hn : 0 ≤ a.val := by nlinarith [sq_nonneg x]
    exact lt_of_le_of_ne hn (Ne.symm a.ne_zero)
  · intro ha
    exact isQuadraticNorm_of_isSquare_right ℝ (real_isSquare_of_nonneg a ha.le)

/-- The negative-parameter real norm subgroup has two cosets. -/
theorem real_index_two (theta : ℝˣ) (htheta : theta.val < 0) :
    (quadraticNormGroup ℝ theta).index = 2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨-1, ?_, ?_⟩
  · rw [mem_quadraticNormGroup, real_norm_iff_positive theta htheta]
    norm_num
  · intro a
    by_cases ha : 0 < a.val
    · exact Or.inr ((real_norm_iff_positive theta htheta a).mpr ha)
    · left
      apply (real_norm_iff_positive theta htheta (a * -1)).mpr
      have hneg : a.val < 0 := lt_of_le_of_ne (le_of_not_gt ha) a.ne_zero
      simpa only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one]
        using neg_pos.mpr hneg

/-- The complete real local index formula, stated using squareness. -/
theorem real_index (theta : ℝˣ) :
    (quadraticNormGroup ℝ theta).index =
      (by
        classical
        exact if IsSquare theta then 1 else 2) := by
  classical
  split_ifs with hs
  · exact LocalNormIndices.quadraticNormGroup_index_one theta hs
  · exact real_index_two theta (lt_of_not_ge (fun h ↦ hs (real_isSquare_of_nonneg theta h)))

/-- Every complex unit is a square; this includes every complex parameter. -/
theorem complex_isSquare (a : ℂˣ) : IsSquare a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a.val (by decide : 0 < 2)
  have hz0 : z ≠ 0 := by
    intro h
    exact a.ne_zero (by simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hz.symm)
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  change a.val = z * z
  simpa only [← pow_two] using hz.symm

variable {K : Type*} [Field K] [NumberField K]

/-- Every actual infinite completion has index one or two according to
local squareness, with no real or complex norm law assumed. -/
theorem quadraticNormGroup_index (v : NumberField.InfinitePlace K) (theta : v.Completionˣ) :
    (quadraticNormGroup v.Completion theta).index =
      (by
        classical
        exact if IsSquare theta then 1 else 2) := by
  classical
  split_ifs with hs
  · exact LocalNormIndices.quadraticNormGroup_index_one theta hs
  · rcases v.isReal_or_isComplex with hr | hc
    · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hr
      rw [index_map _ _ e theta, real_index]
      have hn : ¬ IsSquare (Units.map e.toMonoidHom theta) := by
        intro h
        have h' := h.map (Units.mapEquiv e.toMulEquiv).symm.toMonoidHom
        change IsSquare ((Units.mapEquiv e.toMulEquiv).symm
          ((Units.mapEquiv e.toMulEquiv) theta)) at h'
        exact hs (by simpa only [MulEquiv.symm_apply_apply] using h')
      exact if_neg hn
    · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
      have h := (complex_isSquare (Units.map e.toMonoidHom theta)).map
        (Units.mapEquiv e.toMulEquiv).symm.toMonoidHom
      change IsSquare ((Units.mapEquiv e.toMulEquiv).symm
        ((Units.mapEquiv e.toMulEquiv) theta)) at h
      exact (hs (by simpa only [MulEquiv.symm_apply_apply] using h)).elim

universe u
variable {F : Type u} [Field F] [NumberField F]

/-- The actual quadratic extension fiber at an infinite place has this index. -/
theorem infinite_index (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace F) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (infinitePlaceFiberNormUnits (E := QuadraticAlgebra F theta.val 0) v).range.index =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap F v.Completion).toMonoidHom theta)
          then 1 else 2) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have heq : (infinitePlaceFiberNormUnits (E := QuadraticAlgebra F theta.val 0) v).range =
      quadraticNormGroup v.Completion
        (Units.map (algebraMap F v.Completion).toMonoidHom theta) := by
    ext a
    exact CompletedNormImages.infinite_norm_range_iff theta htheta v a
  rw [heq]
  exact quadraticNormGroup_index v _

end NormEuclidean.InfiniteNormIndices
