import NormEuclidean.RamifiedBinaryDensity
import Bong.Dyadic.NumberFieldCompletion

/-!
# Local binary factors at actual number-field places

The completed residue cardinality is identified with the absolute ideal
norm. The odd unimodular factors and their finite products are proved for
actual congruence counts. This does not identify an infinite Euler product
at one or the ordinary genus class-sum mass with a product of local factors.
-/

noncomputable section

namespace NormEuclidean.BinaryPlaceDensity

open IsDedekindDomain IsLocalRing UnramifiedBinaryDensity
open Bong.NumberFieldCompletion
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The actual completed residue cardinality is the prime's absolute ideal norm. -/
theorem residue_card (p : HeightOneSpectrum (𝓞 K)) :
    Nat.card (ResidueField (integerRing p)) = Ideal.absNorm p.asIdeal := by
  letI := Ideal.Quotient.field p.asIdeal
  let e := RingEquiv.ofBijective (residueQuotientMap p)
    ⟨(residueQuotientMap p).injective, residueQuotientMap_surjective p⟩
  exact (Nat.card_congr e.toEquiv).symm.trans (Ideal.absNorm_apply p.asIdeal).symm

/-- Avoiding the dyadic primes gives invertibility of two in the completed ring. -/
theorem two_isUnit (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∉ p.asIdeal) :
    IsUnit (2 : integerRing p) := by
  letI := Ideal.Quotient.field p.asIdeal
  have hq : (2 : 𝓞 K ⧸ p.asIdeal) ≠ 0 := by
    change Ideal.Quotient.mk p.asIdeal (2 : 𝓞 K) ≠ 0
    exact Ideal.Quotient.eq_zero_iff_mem.not.mpr hp
  apply (residue_ne_zero_iff_isUnit _).mp
  have h := (residueQuotientMap p).injective.ne hq
  simpa only [map_ofNat, map_zero] using h

/-- The residue character of the actual binary norm parameter. -/
def character (p : HeightOneSpectrum (𝓞 K)) (d : integerRing p) : ℤ := by
  classical
  exact if residue (integerRing p) d = 0 then 0
    else if IsSquare (residue (integerRing p) d) then 1 else -1

/-- Every positive congruence level gives the Euler factor at an odd unimodular place. -/
theorem unimodular_factor (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∉ p.asIdeal) (d : integerRing p) (hd : IsUnit d) (n : ℕ) :
    levelDensity (integerRing p) d n =
      1 - (character p d : ℝ) / Ideal.absNorm p.asIdeal := by
  have hne := (residue_ne_zero_iff_isUnit d).mpr hd
  by_cases hs : IsSquare (residue (integerRing p) d)
  · obtain ⟨s, he⟩ := hs
    have he2 : s ^ 2 = residue (integerRing p) d := by simpa [pow_two] using he.symm
    rw [split_level (integerRing p) d hd (two_isUnit p hp) s he2 n, residue_card p]
    simp [character, hne, show IsSquare (residue (integerRing p) d) from ⟨s, he⟩]
  · rw [nonsplit_level (integerRing p) d hd (two_isUnit p hp) hs n, residue_card p]
    simp [character, hne, hs]
    ring

/-- At odd places a parameter of positive valuation r has factor 2 (Np)^r
at every level above r, with the valuation given by the actual principal ideal. -/
theorem ramified_factor (p : HeightOneSpectrum (𝓞 K))
    (hp : (2 : 𝓞 K) ∉ p.asIdeal) (d : integerRing p) (r n : ℕ) (hr : 0 < r)
    (hd : Ideal.span ({d} : Set (integerRing p)) = maximalIdeal (integerRing p) ^ r) :
    levelDensity (integerRing p) d (r + n) = 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ r := by
  rw [RamifiedBinaryDensity.ramified_level (integerRing p) d (two_isUnit p hp) r n hr hd,
    residue_card p]

/-- The good part of a finite local-density product is the corresponding finite
Euler product, with no limiting or global mass assumption. -/
theorem finite_unimodular_product (S : Finset (HeightOneSpectrum (𝓞 K)))
    (d : (p : HeightOneSpectrum (𝓞 K)) → integerRing p)
    (n : HeightOneSpectrum (𝓞 K) → ℕ)
    (hodd : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) (hd : ∀ p ∈ S, IsUnit (d p)) :
    ∏ p ∈ S, levelDensity (integerRing p) (d p) (n p) =
      ∏ p ∈ S, (1 - (character p (d p) : ℝ) / Ideal.absNorm p.asIdeal) := by
  exact Finset.prod_congr rfl fun p hp ↦ unimodular_factor p (hodd p hp) (d p) (hd p hp) _

/-- A global integer avoiding the prime is a unit in the actual completed integer ring. -/
theorem integer_isUnit (p : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) (hd : d ∉ p.asIdeal) :
    IsUnit (integerEmbedding p d) := by
  letI := Ideal.Quotient.field p.asIdeal
  apply (residue_ne_zero_iff_isUnit _).mp
  change residueQuotientMap p (Ideal.Quotient.mk p.asIdeal d) ≠ 0
  intro h
  have he := (residueQuotientMap p).injective (h.trans (map_zero _).symm)
  exact hd (Ideal.Quotient.eq_zero_iff_mem.mp he)

/-- For a fixed nonzero global integral parameter, the dyadic and nonunit
places are contained in the explicit finite set of prime divisors of 2d. -/
theorem finite_exceptional_places (d : 𝓞 K) (hd : d ≠ 0) :
    {p : HeightOneSpectrum (𝓞 K) | 2 * d ∈ p.asIdeal}.Finite := by
  have h : (Ideal.span ({2 * d} : Set (𝓞 K))) ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using
      mul_ne_zero (show (2 : 𝓞 K) ≠ 0 by norm_num) hd
  simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using Ideal.finite_factors h

/-- Outside those explicit exceptions, every positive level has the proved Euler factor. -/
theorem global_parameter_factor (d : 𝓞 K) (p : HeightOneSpectrum (𝓞 K))
    (hp : 2 * d ∉ p.asIdeal) (n : ℕ) :
    levelDensity (integerRing p) (integerEmbedding p d) n =
      1 - (character p (integerEmbedding p d) : ℝ) / Ideal.absNorm p.asIdeal := by
  have h2 : (2 : 𝓞 K) ∉ p.asIdeal := fun h ↦ hp (Ideal.mul_mem_right d _ h)
  have hd : d ∉ p.asIdeal := fun h ↦ hp (Ideal.mul_mem_left _ _ h)
  exact unimodular_factor p h2 _ (integer_isUnit p d hd) n

end NormEuclidean.BinaryPlaceDensity
