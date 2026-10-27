import NormEuclidean.ChapterX.NormPrimeChain

/-!
# The actual ascending norm-subgroup chain

Separating primes construct the entire strict chain inside principal
times actual extension norms. Its length is the base S-unit rank.
The remaining numerical input for 65:21 is precisely the initial
square-idele index computation 65:12.
-/

noncomputable section

namespace NormEuclidean.QuadraticNormPrimeChain

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SquareIdeles NormPrimeChain
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Square S-ideles are actual quadratic norms at every good constrained prime. -/
theorem squareS_le_norm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) (hunit : theta ∈ sUnitSubgroup S) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    squareS S ≤ (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro i hi
  apply (NormFiberAssembly.mem_full_norm_range_iff theta htheta i).mpr
  constructor
  · intro p
    by_cases hp : p ∈ S
    · exact GoodPlaceNorms.isQuadraticNorm_of_units p (htwo p hp) _ _
        ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p theta.val).trans (hunit p hp))
        (hi.1 p hp)
    · exact Bong.Dyadic.isQuadraticNorm_of_isSquare_right _ (hi.2.1 p hp)
  · exact fun v ↦ Bong.Dyadic.isQuadraticNorm_of_isSquare_right _ (hi.2.2 v)

/-- Ideles supported on split primes belong to the actual full norm image. -/
theorem supported_le_norm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (T : Set (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ p ∈ T, IsSquare
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    supported T ≤ (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro i hi
  apply (NormFiberAssembly.mem_full_norm_range_iff theta htheta i).mpr
  constructor
  · intro p
    by_cases hp : p ∈ T
    · exact Bong.Dyadic.isQuadraticNorm_of_isSquare_left _ (hT p hp)
    · rw [hi.1 p hp]
      exact Bong.Dyadic.isQuadraticNorm_one _ _
  · intro v
    rw [hi.2 v]
    exact Bong.Dyadic.isQuadraticNorm_one _ _

/-- The strict chain in 65:21 is constructed from actual S-units and actual ideles. -/
theorem exists_strict_chain (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) (hunit : theta ∈ sUnitSubgroup S)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    let r := Module.finrank ℤ (Additive (sUnitSubgroup S))
    ∃ H : ℕ → Subgroup (NumberFieldIdele K),
      H 0 = idelePrincipalEmbedding.range ⊔ squareS S ∧
      (∀ i < r, H i < H (i + 1)) ∧
      H r ≤ idelePrincipalEmbedding.range ⊔
        (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range := by
  classical
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let r := Module.finrank ℤ (Additive (sUnitSubgroup S))
  obtain ⟨e, i₀, p, he₀, hsep, hinj⟩ :=
    SeparatingSUnitPrimes.exists_separating_family S hS htwo theta htheta hunit
  let J := {i : Fin (r + 1) // i ≠ i₀}
  have hJ : Fintype.card J = r := by simp [J]
  let f : Fin r ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  let T (k : ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
    {q | ∃ j : Fin r, j.val < k ∧ p (f j).val = q}
  let H (k : ℕ) := group S (T k)
  have hT (k : ℕ) : T k ⊆ Set.range p := by
    rintro q ⟨j, _, rfl⟩
    exact ⟨(f j).val, rfl⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · have ht : T 0 = ∅ := by ext q; simp [T]
    change group S (T 0) = _
    rw [ht, group_empty]
  · intro k hk
    let j : Fin r := ⟨k, hk⟩
    have hmono : T k ⊆ T (k + 1) := by
      rintro q ⟨l, hl, rfl⟩
      exact ⟨l, by omega, rfl⟩
    apply group_strict S e p hsep htwo hprincipal (T k) (T (k + 1)) (hT k) hmono
      (p (f j).val) ⟨(f j).val, rfl⟩ (hsep.1 (f j).val)
    · rintro ⟨l, hl, heq⟩
      have hlj : l = j := f.injective (Subtype.ext (hinj heq))
      have hv := congrArg Fin.val hlj
      change l.val = k at hv
      omega
    · exact ⟨j, Nat.lt_succ_self k, rfl⟩
  · have hsplit : ∀ q ∈ T r, IsSquare
        (Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom theta) := by
      rintro q ⟨j, _, rfl⟩
      have h := hsep.2.2 (f j).val i₀ (f j).property
      rwa [he₀] at h
    exact sup_le le_sup_left (sup_le
      ((squareS_le_norm theta htheta S htwo hunit).trans le_sup_right)
      ((supported_le_norm theta htheta (T r) hsplit).trans le_sup_right))

/-- Once 65:12 supplies the initial square index, the actual strict chain proves 65:21. -/
theorem index_two_of_square_index (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) (hunit : theta ∈ sUnitSubgroup S)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤)
    (hindex : (idelePrincipalEmbedding.range ⊔ squareS S).index =
      2 ^ (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
      (E := QuadraticAlgebra K theta.val 0)).range).index = 2 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨H, hzero, hstrict, hle⟩ := exists_strict_chain theta htheta S hS htwo hunit hprincipal
  have hu := NormIndexReduction.strict_chain_index_le_two H _ _
    (hzero ▸ hindex) hstrict hle
  have hl := (QuadraticNormIndexExact.global_index_finite_lower_bound theta htheta).1
  omega

end NormEuclidean.QuadraticNormPrimeChain
