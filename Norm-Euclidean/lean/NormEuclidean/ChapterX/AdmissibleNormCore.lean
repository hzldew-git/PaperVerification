import NormEuclidean.ChapterX.ExtensionNormPrincipalization
import NormEuclidean.ChapterX.CofiniteLocalIsotropy

/-!
# Admissible cofinite cores for the quadratic norm argument

The actual base and extension principalization results can be imposed
simultaneously with every finite exclusion, oddness and unit conditions on
a prescribed quadratic parameter. This supplies the choice of `S` needed
before the index computation in 65:13; the index computation is still separate.
-/

noncomputable section

namespace NormEuclidean.ExtensionIdeleNorm

open IsDedekindDomain
open scoped NumberField

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- There is an actual finite prime of the ring of integers. -/
theorem exists_finite_prime : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨p, hp0, hpmax⟩ :=
    Ring.exists_maximal_of_not_isField (NumberField.RingOfIntegers.not_isField K)
  exact ⟨⟨p, hpmax.isPrime, hp0⟩⟩

/-- Only finitely many finite primes of a number field are dyadic. -/
theorem finite_dyadic_primes :
    {p : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ p.asIdeal}.Finite := by
  have htwo : (2 : 𝓞 K) ≠ 0 := by norm_num
  have hI : (Ideal.span {(2 : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using htwo
  apply (Ideal.finite_factors hI).subset
  intro p hp
  exact Ideal.dvd_iff_le.mpr (p.asIdeal.span_singleton_le_iff_mem.mpr hp)

/-- A cofinite proper set avoids any finite exceptional set and the dyadic and
nonunit places of `theta`, retaining base and extension principalization on every subset. -/
theorem exists_admissible_common_core (theta : Kˣ)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧ S₀ ≠ Set.univ ∧
      Disjoint S₀ T ∧ (∀ p ∈ S₀, (2 : 𝓞 K) ∉ p.asIdeal) ∧
      (∀ p ∈ S₀, p.valuation K (theta : K) = 1) ∧
      ∀ S : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S₀ →
        (idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤) ∧
        (idelePrincipalEmbedding.range ⊔
          finitePlaceSIdeleSubgroup (finitePlacesOverSet (E := E) S) = ⊤) := by
  obtain ⟨P, hP, hprincipal⟩ := exists_common_principalization_core (K := K) (E := E)
  obtain ⟨p₀⟩ := exists_finite_prime (K := K)
  let bad : Set (HeightOneSpectrum (𝓞 K)) := T ∪
    {p | (2 : 𝓞 K) ∈ p.asIdeal} ∪ {p | p.valuation K (theta : K) ≠ 1} ∪ {p₀}
  have hbad : bad.Finite :=
    ((hT.union finite_dyadic_primes).union
      (CofiniteLocalIsotropy.finite_nonunit_valuations (theta : K) (Units.ne_zero theta))).union
        (Set.finite_singleton p₀)
  let S₀ := P \ bad
  refine ⟨S₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (P \ bad)ᶜ.Finite
    rw [Set.compl_sdiff]
    exact hbad.union hP
  · intro htop
    have hp : p₀ ∈ S₀ := by simp [htop]
    exact hp.2 (by simp [bad])
  · apply Set.disjoint_left.mpr
    intro p hp hpT
    exact hp.2 (by simp [bad, hpT])
  · intro p hp hp2
    exact hp.2 (by simp [bad, hp2])
  · intro p hp
    by_contra hunit
    exact hp.2 (by simp [bad, hunit])
  · intro S hS
    exact hprincipal S (hS.trans Set.sdiff_subset)

end NormEuclidean.ExtensionIdeleNorm
