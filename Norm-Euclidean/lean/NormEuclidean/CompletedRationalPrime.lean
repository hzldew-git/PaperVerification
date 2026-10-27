import NormEuclidean.CompletedPadicBase
import NormEuclidean.CompletedPrimeIdeals
import NormEuclidean.CompletedTensorProduct
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The actual residue characteristic is the prime below the original completion

The rational prime is identified by its membership in the defining
global prime and by the actual completed residue map. This will let
the canonical completed-tensor coefficient maps be compared with the
previously constructed actual Q_p and Z_p coefficient maps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedRationalPrime

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open CompletedPadicBase CompletedTensorProduct
open scoped NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The underlying rational finite place of the actual global prime. -/
def below (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 ℚ) :=
  finitePlaceBelow (K := ℚ) v

/-- The rational prime attached to a rational finite place by its actual ideal generator. -/
def prime (q : HeightOneSpectrum (𝓞 ℚ)) : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv q

theorem prime_mem (q : HeightOneSpectrum (𝓞 ℚ)) : (prime q : 𝓞 ℚ) ∈ q.asIdeal := by
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff q).mp
    (dvd_refl (Rat.HeightOneSpectrum.natGenerator q))
  apply (Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).mp
  rw [map_natCast]
  change (Rat.HeightOneSpectrum.natGenerator q : ℤ) ∈ _
  exact h

/-- The originally constructed local residue characteristic equals the original prime below it. -/
theorem rationalPrime_eq (v : HeightOneSpectrum (𝓞 F)) :
    rationalPrime v = prime (below v) := by
  let p := prime (below v)
  have hq := prime_mem (below v)
  change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ v.asIdeal at hq
  have hv : (p : 𝓞 F) ∈ v.asIdeal := by simpa only [map_natCast] using hq
  have hm := (CompletedPrimeIdeals.embedding_mem_maximal v (p : 𝓞 F)).mpr hv
  have hz : IsLocalRing.residue (integerRing v) (integerEmbedding v (p : 𝓞 F)) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hp0 : (p : IsLocalRing.ResidueField (integerRing v)) = 0 := by
    simpa only [map_natCast] using hz
  change ringChar (IsLocalRing.ResidueField (integerRing v)) = p
  exact CharP.ringChar_of_prime_eq_zero p.2 hp0

/-- Every factor of the rational-place tensor decomposition uses that same rational prime. -/
theorem factor_rationalPrime (q : HeightOneSpectrum (𝓞 ℚ)) (w : Place F q) :
    rationalPrime (CompletedTensorProduct.prime F q w) = prime q := by
  rw [rationalPrime_eq]
  exact congrArg (fun q ↦ (prime q : ℕ)) (finitePlaceBelow_finitePlaceExtensionCentre q w)

end NormEuclidean.CompletedRationalPrime
