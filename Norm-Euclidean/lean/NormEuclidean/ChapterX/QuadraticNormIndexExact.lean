import NormEuclidean.ChapterX.SUnitExactIndex
import NormEuclidean.ChapterX.SUnitIdeleIndex

/-!
# O'Meara 65:13 for actual quadratic ideles

The local norm indices and the exact S-unit index are now proved inputs.
The formula uses literal principal and S-idele norm subgroups. Admissible
common cores supply both principalization conditions for every shrinking.
-/

noncomputable section

namespace NormEuclidean.QuadraticNormIndexExact

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm PrincipalNormComponents
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The literal 65:13 index formula, with both arithmetic index values proved. -/
theorem index_formula (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let P : Subgroup (NumberFieldIdele K) := idelePrincipalEmbedding.range
    let U := finitePlaceSIdeleSubgroup S
    let A := sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S
    let C := principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S
    P ⊔ U = ⊤ →
      idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup
        (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) = ⊤ →
      (P ⊔ (extensionIdeleNorm (K := K)
        (E := QuadraticAlgebra K theta.val 0)).range).index =
          2 * C.relIndex ((P ⊓ U) ⊓ A) ∧ C.relIndex ((P ⊓ U) ⊓ A) ≠ 0 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  dsimp only
  intro hbase hsource
  obtain ⟨hb, hi⟩ := SUnitExactIndex.norm_index theta htheta S hS htwo hunit hbase
  apply QuadraticNormIndex.formula_of_local_unit_indices theta htheta S hbase hsource
    (SNormIndex.nonsplitCount theta S hS) hb
    (SNormIndex.index_eq_pow theta htheta S hS htwo hunit)
  exact (SUnitIdeleIndex.principal_norm_index_eq theta htheta S).trans hi

/-- A cofinite admissible common core proves 65:13 on every cofinite shrinking. -/
theorem exists_core_formula (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧ S₀ ≠ Set.univ ∧
      Disjoint S₀ T ∧ ∀ S ⊆ S₀, Sᶜ.Finite →
        (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
          (E := QuadraticAlgebra K theta.val 0)).range).index =
          2 * (principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
            ((idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
              sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S) ∧
          (principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
            ((idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
              sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S) ≠ 0 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨S₀, hcof, hproper, hdis, htwo, hunit, hprincipal⟩ :=
    exists_admissible_common_core (E := QuadraticAlgebra K theta.val 0) theta T hT
  refine ⟨S₀, hcof, hproper, hdis, fun S hS hcofS ↦ ?_⟩
  exact index_formula theta htheta S hcofS (fun p hp ↦ htwo p (hS hp))
    (fun p hp ↦ hunit p (hS hp)) (hprincipal S hS).1 (hprincipal S hS).2

/-- In particular the actual global idele norm index is finite and at least two. -/
theorem global_index_finite_lower_bound (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let d := (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
      (E := QuadraticAlgebra K theta.val 0)).range).index
    2 ≤ d ∧ d ≠ 0 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨S, hcof, _, _, h⟩ := exists_core_formula theta htheta ∅ Set.finite_empty
  obtain ⟨hd, hn⟩ := h S le_rfl hcof
  dsimp only
  rw [hd]
  constructor
  · omega
  · exact mul_ne_zero (by decide) hn

end NormEuclidean.QuadraticNormIndexExact
