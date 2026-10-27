import NormEuclidean.ChapterX.OddNormObstruction
import NormEuclidean.ChapterX.CompletedNormImages
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.GroupTheory.Index

/-!
# Quadratic local norm indices at split and good odd places

Split fibers have index one at every finite and infinite place. At an odd
finite place with a unit parameter, the norm index is one for a square
parameter and two otherwise. Dyadic nonsplit indices remain separate.
-/

noncomputable section

namespace NormEuclidean.LocalNormIndices

open IsDedekindDomain QuadraticExtensionNorm ExtensionIdeleNorm Bong.Dyadic
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- A uniformizer exists as a unit of the actual completed field. -/
theorem exists_uniformizer (p : HeightOneSpectrum (𝓞 K)) :
    ∃ pi : (p.adicCompletion K)ˣ, Valued.v pi.val = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K p
    (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro h
    exact (WithZero.exp_ne_zero : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0)
      (by simpa only [h, map_zero] using hx.symm)
  exact ⟨Units.mk0 x hx0, hx⟩

/-- Unit norms and square factors represent every element of even valuation. -/
theorem norm_of_even_valuation (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta : (p.adicCompletion K)ˣ)
    (htheta : Valued.v theta.val = 1) (pi : (p.adicCompletion K)ˣ)
    (hpi : Valued.v pi.val = WithZero.exp (-1 : ℤ))
    (a : (p.adicCompletion K)ˣ) (ha : Even (WithZero.log (Valued.v a.val))) :
    IsQuadraticNorm (p.adicCompletion K) theta a := by
  obtain ⟨k, hk⟩ := ha
  let q := pi ^ k
  have hq : Valued.v q.val = WithZero.exp (-k) := by
    dsimp only [q]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hpi, ← WithZero.exp_zsmul]
    congr 1
    simp only [Int.zsmul_eq_mul, mul_neg, mul_one]
  let b := a * (q * q)
  have hb : Valued.v b.val = 1 := by
    change Valued.v (a.val * (q.val * q.val)) = 1
    have hva : Valued.v a.val ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
    rw [map_mul, map_mul, hq, ← WithZero.exp_log hva,
      ← WithZero.exp_add, ← WithZero.exp_add]
    rw [hk]
    have hz : k + k + (-k + -k) = 0 := by ring
    rw [hz, WithZero.exp_zero]
  have hn : IsQuadraticNorm (p.adicCompletion K) theta b :=
    GoodPlaceNorms.isQuadraticNorm_of_units p htwo theta b htheta hb
  have hs : IsQuadraticNorm (p.adicCompletion K) theta (q * q) :=
    isQuadraticNorm_of_isSquare_right _ ⟨q, rfl⟩
  have h := IsQuadraticNorm.mul _ hn (IsQuadraticNorm.inv _ hs)
  simpa only [b, mul_inv_cancel_right] using h

/-- The norm subgroup has index two for a nonsquare unit parameter at
an odd actual finite completion. The uniformizer is proved not to be a norm. -/
theorem quadraticNormGroup_index_two (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta : (p.adicCompletion K)ˣ)
    (htheta : Valued.v theta.val = 1) (hnonsquare : ¬ IsSquare theta) :
    (quadraticNormGroup (p.adicCompletion K) theta).index = 2 := by
  obtain ⟨pi, hpi⟩ := exists_uniformizer p
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨pi, fun h ↦ hnonsquare
    (OddNormObstruction.square_of_uniformizer_norm p htwo theta pi htheta hpi h), ?_⟩
  intro a
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (WithZero.log (Valued.v a.val))
  · right
    exact norm_of_even_valuation p htwo theta htheta pi hpi a
      ⟨k, by simpa only [two_mul] using hk⟩
  · left
    apply norm_of_even_valuation p htwo theta htheta pi hpi (a * pi)
    refine ⟨k, ?_⟩
    change WithZero.log (Valued.v (a.val * pi.val)) = k + k
    rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr a.ne_zero)
      ((Valuation.ne_zero_iff _).mpr pi.ne_zero), hpi, WithZero.log_exp, hk]
    ring

/-- Split quadratic norm subgroups have index one over every field of
characteristic zero; this does not use a local norm law. -/
theorem quadraticNormGroup_index_one {F : Type*} [Field F] [CharZero F]
    (theta : Fˣ) (htheta : IsSquare theta) : (quadraticNormGroup F theta).index = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  exact isQuadraticNorm_of_isSquare_left F htheta

universe u
variable {F : Type u} [Field F] [NumberField F]

/-- All finite split fibers have actual completed norm index one, including
dyadic split fibers. -/
theorem finite_split_index (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 F))
    (hsplit : IsSquare (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (finitePlaceFiberNormUnits (E := QuadraticAlgebra F (theta : F) 0) p).range.index = 1 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply Subgroup.index_eq_one.mpr
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  exact (CompletedNormImages.finite_norm_range_iff theta htheta p a).mpr
    (isQuadraticNorm_of_isSquare_left _ hsplit)

/-- At good finite primes the actual completed norm index is computed,
with no local norm-index premise. -/
theorem finite_good_index (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 F)) (htwo : (2 : 𝓞 F) ∉ p.asIdeal)
    (hunit : p.valuation F theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (finitePlaceFiberNormUnits (E := QuadraticAlgebra F (theta : F) 0) p).range.index =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom theta)
          then 1 else 2) := by
  classical
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have heq : (finitePlaceFiberNormUnits (E := QuadraticAlgebra F (theta : F) 0) p).range =
      quadraticNormGroup (p.adicCompletion F)
        (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom theta) := by
    ext a
    exact CompletedNormImages.finite_norm_range_iff theta htheta p a
  rw [heq]
  split_ifs with hs
  · exact quadraticNormGroup_index_one _ hs
  · apply quadraticNormGroup_index_two p htwo _ _ hs
    change Valued.v (algebraMap F (p.adicCompletion F) theta.val) = 1
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p theta.val).trans hunit

/-- Actual infinite split fibers have norm index one. -/
theorem infinite_split_index (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace F)
    (hsplit : IsSquare (Units.map (algebraMap F v.Completion).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (infinitePlaceFiberNormUnits (E := QuadraticAlgebra F (theta : F) 0) v).range.index = 1 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply Subgroup.index_eq_one.mpr
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  exact (CompletedNormImages.infinite_norm_range_iff theta htheta v a).mpr
    (isQuadraticNorm_of_isSquare_left _ hsplit)

end NormEuclidean.LocalNormIndices
