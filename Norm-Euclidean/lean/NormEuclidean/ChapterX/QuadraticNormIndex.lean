import NormEuclidean.ChapterX.QuadraticPrincipalNorm
import NormEuclidean.ChapterX.NormIndexReduction

/-!
# Actual quadratic idele index reduction for O'Meara 65:13

The subgroups here are norms of actual extension S-ideles and actual
principal extension S-ideles. Principal compatibility is proved internally.
The index balance is unconditional on the proved principalization cores.
The final formula still requires the local and S-unit index computations.
-/

noncomputable section

namespace NormEuclidean.QuadraticNormIndex

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm PrincipalNormComponents
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- After source principalization, principal times all norms equals
principal times the actual S-norm image. -/
theorem principal_sup_norm_range (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    idelePrincipalEmbedding.range ⊔
        finitePlaceSIdeleSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K (theta : K) 0) S)
          = ⊤ →
      idelePrincipalEmbedding.range ⊔
        (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K (theta : K) 0)).range =
      idelePrincipalEmbedding.range ⊔
        sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro hS
  have hD : (idelePrincipalEmbedding.comp
      (globalNormUnits (K := K) (E := QuadraticAlgebra K (theta : K) 0))).range ≤
        idelePrincipalEmbedding.range := by
    rintro i ⟨x, rfl⟩
    exact ⟨globalNormUnits (K := K) x, rfl⟩
  rw [← QuadraticPrincipalNorm.norm_range_generation theta htheta S hS,
    ← sup_assoc, sup_of_le_left hD]

/-- The exact group-theoretic index identity inside the actual idele groups. -/
theorem local_global_balance (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let P : Subgroup (NumberFieldIdele K) := idelePrincipalEmbedding.range
    let U := finitePlaceSIdeleSubgroup S
    let A := sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S
    P ⊔ U = ⊤ →
      idelePrincipalEmbedding.range ⊔
        finitePlaceSIdeleSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K (theta : K) 0) S)
          = ⊤ →
      A.relIndex (P ⊓ U) *
        (P ⊔ (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K (theta : K) 0)).range).index =
          A.relIndex U := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  dsimp only
  intro hbase hsource
  rw [principal_sup_norm_range theta htheta S hsource]
  exact NormIndexReduction.local_global_balance _ _ _ hbase
    ((sIdeleNormSubgroup_le S).trans inf_le_left)

/-- The literal 65:13 formula is reduced to its two missing arithmetic
index computations; neither computation is silently promoted to a theorem. -/
theorem formula_of_local_unit_indices (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let P : Subgroup (NumberFieldIdele K) := idelePrincipalEmbedding.range
    let U := finitePlaceSIdeleSubgroup S
    let A := sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S
    let C := principalSNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S
    P ⊔ U = ⊤ →
      idelePrincipalEmbedding.range ⊔
        finitePlaceSIdeleSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K (theta : K) 0) S)
          = ⊤ →
      ∀ b : ℕ, 0 < b → A.relIndex U = 2 ^ b →
        C.relIndex (P ⊓ U) = 2 ^ (b - 1) →
          (P ⊔ (extensionIdeleNorm (K := K)
            (E := QuadraticAlgebra K (theta : K) 0)).range).index =
              2 * C.relIndex ((P ⊓ U) ⊓ A) ∧ C.relIndex ((P ⊓ U) ⊓ A) ≠ 0 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  dsimp only
  intro hbase hsource b hb hlocal hunit
  rw [principal_sup_norm_range theta htheta S hsource]
  exact NormIndexReduction.formula_of_local_unit_indices _ _ _ _ hbase
    ((sIdeleNormSubgroup_le S).trans inf_le_left)
    (QuadraticPrincipalNorm.principalSNorm_le_intersection theta htheta S)
    b hb hlocal hunit

/-- The actual admissible cofinite cores satisfy the index balance on every
shrinking, with both principalization conditions discharged internally. -/
theorem exists_core_balance (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧ S₀ ≠ Set.univ ∧
      Disjoint S₀ T ∧ (∀ p ∈ S₀, (2 : 𝓞 K) ∉ p.asIdeal) ∧
      (∀ p ∈ S₀, p.valuation K (theta : K) = 1) ∧
      ∀ S ⊆ S₀,
        (sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S).relIndex
            (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) *
          (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
            (E := QuadraticAlgebra K (theta : K) 0)).range).index =
              (sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S).relIndex
                (finitePlaceSIdeleSubgroup S) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨S₀, hcof, hproper, hdis, hodd, hunit, hprincipal⟩ :=
    exists_admissible_common_core (E := QuadraticAlgebra K (theta : K) 0) theta T hT
  refine ⟨S₀, hcof, hproper, hdis, hodd, hunit, ?_⟩
  intro S hS
  exact local_global_balance theta htheta S (hprincipal S hS).1 (hprincipal S hS).2

end NormEuclidean.QuadraticNormIndex
