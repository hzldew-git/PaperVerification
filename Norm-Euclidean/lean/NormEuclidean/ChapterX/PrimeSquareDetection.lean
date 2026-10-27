import NormEuclidean.ChapterX.SquarePrimeSelection

/-!
# O'Meara 65:18a: square detection after deleting separating primes

A family of global S-units with independent local unit square patterns
corrects any S-idele at the selected primes. The proved norm-index lower
bound then detects a global square even when integrality at those primes
has been removed.
-/

noncomputable section

namespace NormEuclidean.PrimeSquareDetection

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

/-- The local square pattern required of a separating family of S-units. -/
def Separates (S : Set (HeightOneSpectrum (𝓞 K))) (e : ι → sUnitSubgroup S)
    (p : ι → HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ i, p i ∈ S) ∧
  (∀ i, ¬ IsSquare (Units.map (algebraMap K ((p i).adicCompletion K)).toMonoidHom
    (e i).val)) ∧
  (∀ i j, i ≠ j → IsSquare
    (Units.map (algebraMap K ((p i).adicCompletion K)).toMonoidHom (e j).val))

/-- A product of the separating S-units corrects arbitrary unit square classes. -/
theorem exists_unit_correction (S : Set (HeightOneSpectrum (𝓞 K)))
    (e : ι → sUnitSubgroup S) (p : ι → HeightOneSpectrum (𝓞 K))
    (h : Separates S e p) (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (j : NumberFieldIdele K) (hj : j ∈ finitePlaceSIdeleSubgroup S) :
    ∃ a : sUnitSubgroup S, ∀ i,
      IsSquare (Units.map (algebraMap K ((p i).adicCompletion K)).toMonoidHom a.val *
        ideleFiniteComponent (p i) j) := by
  classical
  let c (i : ι) : sUnitSubgroup S :=
    if IsSquare (ideleFiniteComponent (p i) j) then 1 else e i
  refine ⟨∏ i, c i, ?_⟩
  intro i
  let f : sUnitSubgroup S →* ((p i).adicCompletion K)ˣ :=
    (Units.map (algebraMap K ((p i).adicCompletion K)).toMonoidHom).comp
      (sUnitSubgroup S).subtype
  have hother : IsSquare (∏ k ∈ Finset.univ.erase i, f (c k)) := by
    apply Finset.isSquare_prod
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    dsimp only [c]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact h.2.2 i k hki.symm
  have hprod : f (∏ k, c k) = f (c i) * ∏ k ∈ Finset.univ.erase i, f (c k) := by
    rw [map_prod]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  change IsSquare (f (∏ k, c k) * ideleFiniteComponent (p i) j)
  rw [hprod]
  by_cases hi : IsSquare (ideleFiniteComponent (p i) j)
  · have hc : f (c i) = 1 := by simp [c, hi]
    rw [hc, one_mul]
    exact hother.mul hi
  · have hc : f (c i) = f (e i) := by simp [c, hi]
    rw [hc]
    have heunit : Valued.v (f (e i)).val = 1 :=
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (p i) (e i).val.val).trans
        ((e i).property (p i) (h.1 i))
    have hpair := QuadraticSquareDescent.nonsquare_unit_product (p i)
      (htwo (p i) (h.1 i)) (f (e i)) (ideleFiniteComponent (p i) j)
      heunit (hj (p i) (h.1 i)) (h.2.1 i) hi
    have hh := hpair.mul hother
    rwa [mul_right_comm (f (e i)) (ideleFiniteComponent (p i) j)] at hh

/-- Local squareness outside S and units away from the separating primes force
global squareness. This is the punctured-core form of O'Meara 65:18a. -/
theorem isSquare_of_punctured_units (S : Set (HeightOneSpectrum (𝓞 K)))
    (e : ι → sUnitSubgroup S) (p : ι → HeightOneSpectrum (𝓞 K))
    (h : Separates S e p) (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤)
    (a : Kˣ)
    (haunit : ∀ q ∈ S, q ∉ Set.range p → q.valuation K a.val = 1)
    (haf : ∀ q ∉ S, IsSquare (algebraMap K (q.adicCompletion K) a.val))
    (hai : ∀ v : NumberField.InfinitePlace K, IsSquare (algebraMap K v.Completion a.val)) :
    IsSquare a := by
  classical
  by_contra hans
  letI := quadraticExtensionField a hans
  letI := quadraticExtensionNumberField a hans
  let P := idelePrincipalEmbedding.range ⊔
    (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K a.val 0)).range
  have hJS : finitePlaceSIdeleSubgroup S ≤ P := by
    intro j hj
    obtain ⟨c, hc⟩ := exists_unit_correction S e p h htwo j hj
    let k := idelePrincipalEmbedding c.val * j
    have hk : k ∈ (extensionIdeleNorm (K := K)
        (E := QuadraticAlgebra K a.val 0)).range := by
      apply (NormFiberAssembly.mem_full_norm_range_iff a hans k).mpr
      constructor
      · intro q
        by_cases hq : q ∈ Set.range p
        · obtain ⟨i, rfl⟩ := hq
          apply Bong.Dyadic.isQuadraticNorm_of_isSquare_right
          simpa only [k, map_mul, PrincipalNormComponents.finiteComponent_principal] using hc i
        · by_cases hqS : q ∈ S
          · apply GoodPlaceNorms.isQuadraticNorm_of_units q (htwo q hqS)
            have hau := haunit q hqS hq
            exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q a.val).trans hau
            change Valued.v (ideleFiniteComponent q k).val = 1
            dsimp only [k]
            rw [map_mul, PrincipalNormComponents.finiteComponent_principal, Units.val_mul,
              map_mul, hj q hqS, mul_one]
            exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q c.val.val).trans
              (c.property q hqS)
          · apply Bong.Dyadic.isQuadraticNorm_of_isSquare_left
            exact (GlobalSquare.unit_square_iff _).mpr (haf q hqS)
      · intro v
        apply Bong.Dyadic.isQuadraticNorm_of_isSquare_left
        exact (GlobalSquare.unit_square_iff _).mpr (hai v)
    have hh := P.mul_mem (Subgroup.mem_sup_left ⟨c.val⁻¹, rfl⟩)
      (Subgroup.mem_sup_right hk)
    simpa only [k, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] using hh
  have htop : P = ⊤ := by
    apply top_unique
    rw [← hprincipal]
    exact sup_le le_sup_left hJS
  have hindex := (QuadraticNormIndexExact.global_index_finite_lower_bound a hans).1
  change 2 ≤ P.index at hindex
  rw [htop, Subgroup.index_top] at hindex
  omega

end NormEuclidean.PrimeSquareDetection
